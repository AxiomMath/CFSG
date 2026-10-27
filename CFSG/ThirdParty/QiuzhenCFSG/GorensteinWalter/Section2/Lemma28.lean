module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970API
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ControlCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma28Helpers
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.PreambleHSU
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Reflection
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma21
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma22
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Theorem26
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.MinimalCounterexample
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section1
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Hall.Basic
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.FinalTheorem

namespace CFSG
end CFSG
open CFSG

/-!
# Lemma 2.8 (Bender, "Finite Groups with Dihedral Sylow 2-Subgroups")

Pinned statement (verbatim from `tasks/gw-lemma28.md`):

    ⁅c.S0, c.U⁆ ≠ ⊥ ∧
      ∀ M : Subgroup G,
        M ≠ ⊤ →
          NormalizerControlledBy c.Hhat M →
            (¬ M ≤ c.Hhat) →
              (c.S : Subgroup G) ≤ M → c.t ∈ componentLayerOf M

The paper's proof (`refs/bender-dihedral-sylow.tex` L281--L287) uses:

* the direct Lemma 2.7 consequence, once the inverted-subgroup hypothesis
  implies `[S, U] ≤ F(U)`;
* for the first assertion, Theorem 2.6 to obtain `Ĥ = H` under
  `[S₀,U]=1`, then Lemma 2.2 to find `1 ≠ X ≤ I_U(s)` with
  `N_G(X) ⊈ Ĥ`, and finally the solvability of `N_G(X)`.

This module keeps that decomposition.  `Lemma28Helpers` supplies the two
elementary inverted-subgroup endpoints.  The commutator transfer, the
required Lemma 2.7 specialization, and both parts of Lemma 2.8 are proved
below without placeholders.
-/

open scoped Pointwise commutatorElement

namespace CFSG.GorensteinWalter

universe u

/-! ## Lemma 2.7 consequence -/

/-- Specialize the proved Lemma 2.7 to a subgroup containing `S`; this
supplies its cardinality alternative and its non-cyclic Sylow hypothesis. -/
private theorem lemma_2_7_consequence_local {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (M : Subgroup G)
    (hMproper : M ≠ ⊤)
    (hN : NormalizerControlledBy c.Hhat M)
    (hnotle : ¬ M ≤ c.Hhat)
    (htnot : c.t ∉ componentLayerOf M)
    (hSle : (c.S : Subgroup G) ≤ M)
    (hSylow : ∀ P : Sylow 2 (↥M), ¬ IsCyclic P) :
    ¬ ⁅(c.S : Subgroup G), c.U⁆ ≤ c.FU := by
  rcases c.dihedralEquiv with ⟨e⟩
  have hcard : Nat.card (↥(c.S : Subgroup G)) = 2 * 2 ^ c.m := by
    exact (Nat.card_congr e.toEquiv).trans DihedralGroup.nat_card
  have hBranch : (8 ≤ Nat.card ↥((c.S : Subgroup G) ⊓ M)) ∨
      Nat.card c.S = 4 ∨ c.t ∈ twoResidualOf M := by
    by_cases hm1 : c.m = 1
    · right
      left
      rw [hcard, hm1]
      norm_num
    · left
      rw [inf_eq_left.mpr hSle, hcard]
      have hm2 : 2 ≤ c.m := by
        have hone : 1 ≤ c.m := c.one_le_m
        omega
      have hpow : 4 ≤ 2 ^ c.m := Nat.pow_le_pow_right (by decide : 0 < 2) hm2
      nlinarith
  exact lemma_2_7_commutator_S_U_not_le_FU hmin c M
    ⟨hMproper, hN, hnotle, htnot, hSylow, hBranch⟩

/-! ## Construction of `Lemma27Hypothesis` (partially proved) -/

/-- The fixed Sylow `2`-subgroup `S` is dihedral, hence not cyclic. -/
private lemma S_not_cyclic {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) :
    ¬ IsCyclic (c.S : Subgroup G) := by
  intro hcyc
  have hcycS : IsCyclic (↥(c.S : Subgroup G)) := by simpa using hcyc
  rcases c.dihedralEquiv with ⟨e⟩
  have hD : IsCyclic (DihedralGroup (2 ^ c.m)) :=
    isCyclic_of_surjective e e.surjective
  rw [DihedralGroup.isCyclic_iff] at hD
  have hpow : 2 ≤ 2 ^ c.m := by
    calc
      2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ c.m := Nat.pow_le_pow_right (by norm_num) c.one_le_m
  have hne : 2 ^ c.m ≠ 1 := by
    intro h1
    have : 2 ≤ (1 : ℕ) := by simpa [h1] using hpow
    norm_num at this
  exact hne hD

/-- If `S ≤ M`, every Sylow `2`-subgroup of `M` is non-cyclic: `S` is a
non-cyclic `2`-subgroup of `M`, it is contained in some Sylow `2`-subgroup,
and all Sylow subgroups are conjugate. -/
private lemma sylow_noncyclic_of_S_le {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (M : Subgroup G)
    (hSle : (c.S : Subgroup G) ≤ M) :
    ∀ P : Sylow 2 (↥M), ¬ IsCyclic P := by
  intro P hPcyc
  let S' : Subgroup (↥M) := (c.S : Subgroup G).subgroupOf M
  have hS'p : IsPGroup 2 S' := by
    exact c.S.isPGroup'.of_equiv (Subgroup.subgroupOfEquivOfLe hSle).symm
  rcases hS'p.exists_le_sylow with ⟨Q, hSleQ⟩
  have hQcyc : IsCyclic (↥(Q : Subgroup (↥M))) := by
    exact isCyclic_of_surjective (Sylow.equiv P Q) (Sylow.equiv P Q).surjective
  have hS'cyc : IsCyclic (↥S') := Subgroup.isCyclic_of_le hSleQ
  have hScyc : IsCyclic (↥(c.S : Subgroup G)) :=
    isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hSle)
      (Subgroup.subgroupOfEquivOfLe hSle).surjective
  exact S_not_cyclic c (by simpa using hScyc)

/-! ## The commutator transfer `[S, U] ≤ F(U)` (proved) -/

/-- Every element of `H = C_G(t)` normalizes `U = O(H)`.  This is the
characteristicity of `O₂'(H)` in `H`, specialized to the fixed setup. -/
private lemma H_normalizes_U {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) {h : G} (hh : h ∈ c.H) :
    ∀ u : G, u ∈ c.U → h * u * h⁻¹ ∈ c.U := by
  intro u hu
  have huH : u ∈ c.H :=
    SetLike.le_def.1 (Subgroup.map_subtype_le (H := c.H) (pPrimeCore 2 c.H)) hu
  have hchar : (pPrimeCore 2 c.H).Characteristic :=
    pPrimeCore_characteristic (p := 2) (G := c.H)
  have hcomap : pPrimeCore 2 c.H ≤
      (pPrimeCore 2 c.H).comap (MulAut.conj ⟨h, hh⟩).toMonoidHom :=
    (Subgroup.characteristic_iff_le_comap.mp hchar) (MulAut.conj ⟨h, hh⟩)
  have huK : (⟨u, huH⟩ : ↥c.H) ∈ pPrimeCore 2 c.H := by
    rcases (Subgroup.mem_map.mp hu) with ⟨y, hy, hyeq⟩
    have hyeq' : (⟨u, huH⟩ : ↥c.H) = y := by
      ext
      simpa using hyeq.symm
    simpa [hyeq'] using hy
  have hconj : (MulAut.conj ⟨h, hh⟩) ⟨u, huH⟩ ∈ pPrimeCore 2 c.H :=
    Subgroup.mem_comap.mp (hcomap huK)
  refine Subgroup.mem_map.mpr ?_
  refine ⟨⟨h * u * h⁻¹,
    c.H.mul_mem (c.H.mul_mem hh huH) (c.H.inv_mem hh)⟩, ?_, rfl⟩
  have hcu : (MulAut.conj ⟨h, hh⟩) ⟨u, huH⟩ =
      (⟨h * u * h⁻¹,
        c.H.mul_mem (c.H.mul_mem hh huH) (c.H.inv_mem hh)⟩ : ↥c.H) := by
    ext
    simp [MulAut.conj_apply, mul_assoc]
  rw [← hcu]
  exact hconj

/-- Every element of `H` normalizes `F(U)`: the Fitting subgroup is
characteristic in `U`, and `U` is normal in `H`. -/
private lemma H_normalizes_FU {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) {h : G} (hh : h ∈ c.H) :
    ∀ f : G, f ∈ c.FU → h * f * h⁻¹ ∈ c.FU := by
  intro f hf
  rcases hf with ⟨y, hy, rfl⟩
  let e : ↥c.U ≃* ↥c.U :=
    { toFun := fun x => ⟨h * x.1 * h⁻¹, H_normalizes_U c hh x.1 x.2⟩
      invFun := fun y => ⟨h⁻¹ * y.1 * h, by
        simpa using H_normalizes_U c (c.H.inv_mem hh) y.1 y.2⟩
      left_inv := by intro x; apply Subtype.ext; group
      right_inv := by intro y; apply Subtype.ext; group
      map_mul' := by intro x y; apply Subtype.ext; change h * (x.1 * y.1) * h⁻¹ =
        (h * x.1 * h⁻¹) * (h * y.1 * h⁻¹); group }
  have hcharF : (fittingSubgroup (↥c.U)).Characteristic :=
    fittingSubgroup_characteristic
  have hle : fittingSubgroup (↥c.U) ≤
      (fittingSubgroup (↥c.U)).comap e.toMonoidHom :=
    (Subgroup.characteristic_iff_le_comap.mp hcharF) e
  have he_y : e y ∈ (fittingSubgroup (↥c.U)) := hle hy
  exact Subgroup.mem_map.mpr ⟨e y, he_y, rfl⟩

/-- The dihedral Sylow subgroup has a reflection. -/
private lemma exists_reflection {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) : ∃ r : G, c.IsReflection r := by
  have hne : c.S0 ≠ (c.S : Subgroup G) := by
    intro heq
    have hcardS0 : Nat.card c.S0 = Nat.card c.S := by rw [heq]
    have hcard : Nat.card (↥(c.S : Subgroup G)) = 2 * Nat.card (↥c.S0) := c.S_index_two
    change Nat.card (↥(c.S : Subgroup G)) = 2 * Nat.card (↥c.S0) at hcard
    rw [hcardS0] at hcard
    have hpos : 0 < Nat.card (↥c.S0) := Nat.card_pos
    omega
  have hnotle : ¬ (c.S : Subgroup G) ≤ c.S0 := by
    intro hle
    exact hne (le_antisymm c.S0_le_S hle)
  rcases Set.not_subset.mp hnotle with ⟨r, hrS, hrnot⟩
  exact ⟨r, hrS, hrnot⟩

/-- For a reflection `s`, every commutator `[s, u]` with `u ∈ U` lies in the
inverted subgroup `I_U(s)`, hence in `F(U)`. -/
private lemma reflection_commutator_mem_FU {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) {s : G} (hs : c.IsReflection s)
    (hinverted : ∀ s : G, c.IsReflection s →
      ∃ I : Subgroup G, IsInvertedSubgroup I c.U s) :
    ∀ u : G, u ∈ c.U → ⁅s, u⁆ ∈ c.FU := by
  intro u hu
  rcases hinverted s hs with ⟨I, hI⟩
  have hI_le_FU : I ≤ c.FU :=
    (centralizerSetup_reflection_invertedSubgroup_abelian_normal c hs hI).2.2
  have hcu : ⁅s, u⁆ ∈ c.U := by
    have hsU : s * u * s⁻¹ ∈ c.U :=
      H_normalizes_U c (centralizerSetup_S_le_H c hs.1) u hu
    exact c.U.mul_mem hsU (c.U.inv_mem hu)
  have hsInv : IsInvolution s := centralizerSetup_reflection_isInvolution c hs
  have hss : s * s = 1 := by simpa [pow_two] using hsInv.2
  have hsinv : s⁻¹ = s := by
    calc
      s⁻¹ = s⁻¹ * 1 := by simp
      _ = s⁻¹ * (s * s) := by rw [hss]
      _ = (s⁻¹ * s) * s := by rw [mul_assoc]
      _ = s := by simp
  have hleft : s * (s * u * s * u⁻¹) * s = u * s * u⁻¹ * s := by
    calc
      s * (s * u * s * u⁻¹) * s = (s * s) * u * s * u⁻¹ * s := by group
      _ = u * s * u⁻¹ * s := by rw [hss]; simp
  have hright : (s * u * s * u⁻¹)⁻¹ = u * s * u⁻¹ * s := by
    calc
      (s * u * s * u⁻¹)⁻¹ = u * s⁻¹ * u⁻¹ * s⁻¹ := by group
      _ = u * s * u⁻¹ * s := by rw [hsinv]
  have hinv : s * ⁅s, u⁆ * s⁻¹ = (⁅s, u⁆)⁻¹ := by
    rw [commutatorElement_def, hsinv]
    rw [hleft, hright]
  have hinvmem : ⁅s, u⁆ ∈ invertedElements c.U s := by
    rw [invertedElements]
    exact ⟨hcu, hinv⟩
  have hIeq : (I : Set G) = invertedElements c.U s := by
    simpa [IsInvertedSubgroup] using hI
  have hmemI : ⁅s, u⁆ ∈ I := by
    change ⁅s, u⁆ ∈ (I : Set G)
    rw [hIeq]
    exact hinvmem
  exact hI_le_FU hmemI

/-- Every commutator `[s, u]` with `s ∈ S` and `u ∈ U` lies in `F(U)`: for
reflections this is the inverted-subgroup fact; for `s ∈ S0`, decompose
`s = r·(r·s)` with two reflections and use the commutator product identity
plus `H`-invariance of `F(U)`. -/
private lemma commutator_mem_FU_of_mem_S {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    (hinverted : ∀ s : G, c.IsReflection s →
      ∃ I : Subgroup G, IsInvertedSubgroup I c.U s)
    {s u : G} (hs : s ∈ (c.S : Subgroup G)) (hu : u ∈ c.U) :
    ⁅s, u⁆ ∈ c.FU := by
  by_cases hs0 : s ∈ c.S0
  · rcases exists_reflection c with ⟨r, hr⟩
    have hrsS : r * s ∈ (c.S : Subgroup G) :=
      (c.S : Subgroup G).mul_mem hr.1 (c.S0_le_S hs0)
    have hrsnot : r * s ∉ c.S0 := by
      intro hrs0
      apply hr.2
      have hr_eq : r = (r * s) * s⁻¹ := by group
      rw [hr_eq]
      exact c.S0.mul_mem hrs0 (c.S0.inv_mem hs0)
    have hr_sq : r * r = 1 := by simpa [pow_two] using
      (centralizerSetup_reflection_isInvolution c hr).2
    have hs_eq : s = r * (r * s) := by
      calc
        s = (r * r) * s := by rw [hr_sq]; simp
        _ = r * (r * s) := by rw [mul_assoc]
    rw [hs_eq]
    rw [commutatorElement_mul_left_eq_conj_mul r (r * s) u]
    exact c.FU.mul_mem
      (H_normalizes_FU c (centralizerSetup_S_le_H c hr.1)
        (⁅r * s, u⁆) (reflection_commutator_mem_FU c ⟨hrsS, hrsnot⟩ hinverted u hu))
      (reflection_commutator_mem_FU c hr hinverted u hu)
  · exact reflection_commutator_mem_FU c ⟨hs, hs0⟩ hinverted u hu

/-- The inverted-subgroup assumption implies `[S, U] ≤ F(U)`.  This is the
paper's opening sentence of Lemma 2.8; it is proved here in full. -/
public theorem lemma_2_8_commutator_le_FU {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    (hinverted : ∀ s : G, c.IsReflection s →
      ∃ I : Subgroup G, IsInvertedSubgroup I c.U s) :
    ⁅(c.S : Subgroup G), c.U⁆ ≤ c.FU := by
  rw [Subgroup.commutator_le]
  intro s hs u hu
  exact commutator_mem_FU_of_mem_S c hinverted hs hu

/-! ## `[S0, U] = 1` forces `Ĥ = H` -/

private lemma twoCoreOf_isNormalIn_local {G : Type u} [Group G] [Finite G]
    (N : Subgroup G) : IsNormalIn (twoCoreOf N) N := by
  refine ⟨?_, ?_⟩
  · intro x hx
    rcases (Subgroup.mem_map).1 hx with ⟨f, _hf, hfx⟩
    rw [← hfx]
    change (f : G) ∈ N
    simp
  · intro h hh k hk
    rcases (Subgroup.mem_map).1 hk with ⟨f, hf, hfk⟩
    rw [← hfk]
    have hconj : (⟨h, hh⟩ : ↥N) * f * (⟨h, hh⟩ : ↥N)⁻¹ ∈ pCore 2 N :=
      (pCore_normal (G := N)).conj_mem (n := f) hf (g := ⟨h, hh⟩)
    refine Subgroup.mem_map.mpr ⟨(⟨h, hh⟩ : ↥N) * f * (⟨h, hh⟩ : ↥N)⁻¹, hconj, ?_⟩
    rw [hfk]
    simpa using hfk

private lemma twoCoreOf_le_S_local {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) :
    twoCoreOf c.Hhat ≤ (c.S : Subgroup G) := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSleHhat : (c.S : Subgroup G) ≤ c.Hhat :=
    (centralizerSetup_S_le_H c).trans c.H_le_Hhat
  let S' : Sylow 2 (↥c.Hhat) := (c.S).subtype hSleHhat
  let T : Subgroup (↥c.Hhat) := (twoCoreOf c.Hhat).subgroupOf c.Hhat
  have hTleHhat : twoCoreOf c.Hhat ≤ c.Hhat := qCoreOf_le c.Hhat 2
  have hTnormal : T.Normal := by
    dsimp [T]
    exact Subgroup.normal_subgroupOf_of_le_normalizer
      (H := c.Hhat) (N := twoCoreOf c.Hhat)
      (le_normalizer_of_isNormalIn (qCoreOf_normal_in c.Hhat 2))
  have hTp0 : IsPGroup 2 (twoCoreOf c.Hhat) := by
    change IsPGroup 2 (qCoreOf c.Hhat 2)
    exact qCoreOf_isPGroup c.Hhat 2
  have hTp : IsPGroup 2 T :=
    hTp0.of_equiv (Subgroup.subgroupOfEquivOfLe hTleHhat).symm
  have hTleS' : T ≤ (S' : Subgroup (↥c.Hhat)) :=
    hTp.le_sylow_of_normal S'
  have hTmap : T.map c.Hhat.subtype = twoCoreOf c.Hhat := by
    dsimp [T]
    exact Subgroup.map_subgroupOf_eq_of_le hTleHhat
  intro x hx
  have hxTmap : x ∈ T.map c.Hhat.subtype := by
    simpa [hTmap] using hx
  rcases (Subgroup.mem_map).1 hxTmap with ⟨y, hyT, rfl⟩
  exact (Subgroup.mem_subgroupOf).mp (hTleS' hyT)

private lemma natCard_S0_eq_two_pow_local {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) :
    Nat.card (↥c.S0) = 2 ^ c.m := by
  have hcardS : Nat.card (↥(c.S : Subgroup G)) = 2 * 2 ^ c.m := by
    rcases c.dihedralEquiv with ⟨e⟩
    calc
      Nat.card (↥(c.S : Subgroup G)) = Nat.card (DihedralGroup (2 ^ c.m)) := by
        exact Nat.card_congr e.toEquiv
      _ = 2 * 2 ^ c.m := by
        rw [Nat.card_eq_fintype_card]
        exact DihedralGroup.card
  have hindex : Nat.card (↥(c.S : Subgroup G)) = 2 * Nat.card (↥c.S0) :=
    c.S_index_two
  rw [hcardS] at hindex
  exact (Nat.mul_left_cancel (by norm_num : 0 < 2) hindex).symm

private lemma S0_le_twoCoreOf_of_commutator_eq_bot {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (h26 : CentralizerStructure c)
    (hcomm : ⁅c.S0, c.U⁆ = ⊥) :
    c.S0 ≤ twoCoreOf c.Hhat := by
  have hcent : c.S0 ≤ Subgroup.centralizer (c.U : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hcomm
  have hle : c.S0 ≤
      (c.S : Subgroup G) ⊓ Subgroup.centralizer (c.U : Set G) :=
    le_inf c.S0_le_S hcent
  simpa [h26.2.1] using hle

private lemma involution_mem_S_of_normal_sylow_local {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (hSleHhat : (c.S : Subgroup G) ≤ c.Hhat)
    (hSnormal : IsNormalIn (c.S : Subgroup G) c.Hhat)
    {x : G} (hxH : x ∈ c.Hhat) (hxInv : IsInvolution x) :
    x ∈ (c.S : Subgroup G) := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Sylow 2 (↥c.Hhat) := (c.S).subtype hSleHhat
  have hPnormal : (P : Subgroup (↥c.Hhat)).Normal := by
    dsimp [P]
    exact Subgroup.normal_subgroupOf_of_le_normalizer (H := c.Hhat) (N := c.S)
      (le_normalizer_of_isNormalIn hSnormal)
  let : Unique (Sylow 2 (↥c.Hhat)) := Sylow.unique_of_normal P hPnormal
  let xH : ↥c.Hhat := ⟨x, hxH⟩
  let X : Subgroup (↥c.Hhat) := Subgroup.zpowers xH
  have hxHord : orderOf xH = 2 := by
    apply orderOf_eq_prime
    · apply Subtype.ext
      exact hxInv.2
    · intro hx1
      apply hxInv.1
      exact congrArg Subtype.val hx1
  have hXp : IsPGroup 2 X := by
    apply IsPGroup.of_card (n := 1)
    simp [X, Nat.card_zpowers, hxHord]
  obtain ⟨Q, hXleQ⟩ := IsPGroup.exists_le_sylow hXp
  have hQeq : Q = P := Subsingleton.elim Q P
  have hxQ : xH ∈ (Q : Subgroup (↥c.Hhat)) := hXleQ (Subgroup.mem_zpowers xH)
  have hxP : xH ∈ (P : Subgroup (↥c.Hhat)) := by simpa [hQeq] using hxQ
  exact (Subgroup.mem_subgroupOf).mp hxP

private theorem not_klein_branch_of_commutator_eq_bot {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (h26 : CentralizerStructure c)
    (hcomm : ⁅c.S0, c.U⁆ = ⊥) :
    ¬ (IsKleinFour (pCore 2 c.Hhat) ∧
      Nonempty ((c.Hhat ⧸ (pCore 2 c.Hhat ⊔ pPrimeCore 2 c.Hhat)) ≃*
        DihedralGroup 3)) := by
  intro hright
  let K : Subgroup G := twoCoreOf c.Hhat
  have hKamb : IsKleinFour K := by
    let e : pCore 2 c.Hhat ≃* K :=
      Subgroup.equivMapOfInjective (pCore 2 c.Hhat) c.Hhat.subtype c.Hhat.subtype_injective
    exact {
      card_four := (Nat.card_congr e.toEquiv).symm.trans hright.1.card_four
      exponent_two :=
        (Monoid.exponent_eq_of_mulEquiv e).symm.trans hright.1.exponent_two
    }
  have hS0leK : c.S0 ≤ K := S0_le_twoCoreOf_of_commutator_eq_bot c h26 hcomm
  have hKleS : K ≤ (c.S : Subgroup G) := twoCoreOf_le_S_local c
  have hS0card : Nat.card (↥c.S0) = 2 ^ c.m := natCard_S0_eq_two_pow_local c
  have hS0card_le4 : 2 ^ c.m ≤ 4 := by
    have hle : Nat.card (↥c.S0) ≤ Nat.card (↥K) := Subgroup.card_le_of_le hS0leK
    rwa [hS0card, hKamb.card_four] at hle
  have hm_le2 : c.m ≤ 2 := by
    by_contra hmnot
    have hm3 : 3 ≤ c.m := by omega
    have h8 : 8 ≤ 2 ^ c.m := Nat.pow_le_pow_right (by decide : 0 < 2) hm3
    have hle : (8 : ℕ) ≤ 4 := h8.trans hS0card_le4
    norm_num at hle
  have hm_cases : c.m = 1 ∨ c.m = 2 := by
    have hone : 1 ≤ c.m := c.one_le_m
    omega
  rcases hm_cases with hm1 | hm2
  · have hScard : Nat.card (↥(c.S : Subgroup G)) = 4 := by
      rw [c.S_index_two, hS0card, hm1]
      norm_num
    have hK_eq_S : K = (c.S : Subgroup G) :=
      Subgroup.eq_of_le_of_card_ge (H := K) (K := (c.S : Subgroup G)) hKleS (by
        rw [hScard, hKamb.card_four])
    have hKnorm : IsNormalIn K c.Hhat := twoCoreOf_isNormalIn_local c.Hhat
    have hSnorm : IsNormalIn (c.S : Subgroup G) c.Hhat := by
      simpa [hK_eq_S] using hKnorm
    have hSleHhat : (c.S : Subgroup G) ≤ c.Hhat :=
      (centralizerSetup_S_le_H c).trans c.H_le_Hhat
    rcases lemma_2_1 hmin c with ⟨x, y, hxInv, hyInv, hnotconj⟩
    let xG : G := (x : c.Hhat)
    let yG : G := (y : c.Hhat)
    have hxInvG : IsInvolution xG := by
      refine ⟨?_, ?_⟩
      · intro hx1
        apply hxInv.1
        apply Subtype.ext
        exact hx1
      · exact congrArg Subtype.val hxInv.2
    have hyInvG : IsInvolution yG := by
      refine ⟨?_, ?_⟩
      · intro hy1
        apply hyInv.1
        apply Subtype.ext
        exact hy1
      · exact congrArg Subtype.val hyInv.2
    have hxS : xG ∈ (c.S : Subgroup G) :=
      involution_mem_S_of_normal_sylow_local c hSleHhat hSnorm x.2 hxInvG
    have hyS : yG ∈ (c.S : Subgroup G) :=
      involution_mem_S_of_normal_sylow_local c hSleHhat hSnorm y.2 hyInvG
    have hxK : xG ∈ K := by
      rw [hK_eq_S]
      exact hxS
    have hyK : yG ∈ K := by
      rw [hK_eq_S]
      exact hyS
    have hxC : xG ∈
        (c.S : Subgroup G) ⊓ Subgroup.centralizer (c.U : Set G) := by
      have hxT : xG ∈ twoCoreOf c.Hhat := by simpa [K] using hxK
      simpa [h26.2.1] using hxT
    have hyC : yG ∈
        (c.S : Subgroup G) ⊓ Subgroup.centralizer (c.U : Set G) := by
      have hyT : yG ∈ twoCoreOf c.Hhat := by simpa [K] using hyK
      simpa [h26.2.1] using hyT
    have hKne : K ≠ ⊥ := by
      intro hKbot
      have hcard : Nat.card (↥K) = 1 := by simp [hKbot]
      rw [hKamb.card_four] at hcard
      norm_num at hcard
    have hNorm : Subgroup.normalizer (c.U : Set G) = c.Hhat :=
      theorem26_normalizer_U_eq_Hhat hmin c hKne (lemma_2_2 hmin c).2
    obtain ⟨g, hgH, hconj⟩ :=
      theorem26_involutions_in_C_conjugate hmin c hNorm hxInvG hyInvG hxC hyC
    apply hnotconj
    refine ⟨⟨g, hgH⟩, ?_⟩
    apply Subtype.ext
    exact hconj
  · have hS0card4 : Nat.card (↥c.S0) = 4 := by
      rw [hS0card, hm2]
      norm_num
    have hEq : c.S0 = K :=
      Subgroup.eq_of_le_of_card_ge (H := c.S0) (K := K) hS0leK (by
        rw [hKamb.card_four, hS0card4])
    have hKcyc : IsCyclic K := by
      let e : K ≃* c.S0 := (MulEquiv.subgroupCongr hEq).symm
      exact (MulEquiv.isCyclic e).mpr c.S0_cyclic
    have : IsKleinFour (↥K) := hKamb
    exact IsKleinFour.not_isCyclic hKcyc

private theorem hhat_eq_H_of_commutator_eq_bot {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (h26 : CentralizerStructure c)
    (hcomm : ⁅c.S0, c.U⁆ = ⊥) :
    c.Hhat = c.H := by
  rcases h26.2.2 with hleft | hright
  · exact hleft.2
  · exact False.elim (not_klein_branch_of_commutator_eq_bot hmin c h26 hcomm hright)

private lemma S0_subgroupOf_index_eq_two_local
    {G : Type u} [Group G] [Finite G] (c : CentralizerSetup G) :
    (c.S0.subgroupOf (c.S : Subgroup G)).index = 2 := by
  have hmap :
      (c.S0.subgroupOf (c.S : Subgroup G)).map
          (c.S : Subgroup G).subtype = c.S0 :=
    Subgroup.map_subgroupOf_eq_of_le c.S0_le_S
  have hcard :
      Nat.card ↥(c.S0.subgroupOf (c.S : Subgroup G)) = Nat.card ↥c.S0 := by
    have h := Subgroup.card_subtype (c.S : Subgroup G)
      (c.S0.subgroupOf (c.S : Subgroup G))
    rw [hmap] at h
    exact h.symm
  have hmul := Subgroup.card_mul_index
    (c.S0.subgroupOf (c.S : Subgroup G))
  rw [hcard, c.S_index_two] at hmul
  exact Nat.mul_right_cancel (Nat.card_pos (α := c.S0))
    (by simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul)

private lemma reflection_inverts_subgroup_local
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (hcomm : ⁅c.S0, c.U⁆ = ⊥)
    {s g : G} (hs : c.IsReflection s) (hg : c.IsReflection g)
    {I X : Subgroup G} (hI : IsInvertedSubgroup I c.U s)
    (hXI : X ≤ I) :
    ∀ x : G, x ∈ X → g * x * g⁻¹ = x⁻¹ := by
  have hsgS0 : s * g ∈ c.S0 := by
    have hmem :
        (⟨s, hs.1⟩ : ↥(c.S : Subgroup G)) * ⟨g, hg.1⟩ ∈
          c.S0.subgroupOf (c.S : Subgroup G) := by
      apply (Subgroup.mul_mem_iff_of_index_two
        (S0_subgroupOf_index_eq_two_local c)).2
      simp [Subgroup.mem_subgroupOf, hs.2, hg.2]
    exact Subgroup.mem_subgroupOf.mp hmem
  have hcentU : c.S0 ≤ Subgroup.centralizer (c.U : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hcomm
  have hsInv : IsInvolution s :=
    centralizerSetup_reflection_isInvolution c hs
  have hss : s * s = 1 := by
    simpa [pow_two] using hsInv.2
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  intro x hxX
  have hxI : x ∈ I := hXI hxX
  have hxInvSet : x ∈ invertedElements c.U s := by
    rw [← hI]
    exact hxI
  have hxU : x ∈ c.U := hxInvSet.1
  have hsInvX : s * x * s⁻¹ = x⁻¹ := hxInvSet.2
  have hsgComm : x * (s * g) = (s * g) * x :=
    (Subgroup.mem_centralizer_iff.mp (hcentU hsgS0)) x hxU
  have hsgFix : (s * g) * x * (s * g)⁻¹ = x := by
    rw [← hsgComm]
    group
  calc
    g * x * g⁻¹ = s⁻¹ * ((s * g) * x * (s * g)⁻¹) * s := by group
    _ = s⁻¹ * x * s := by rw [hsgFix]
    _ = s * x * s⁻¹ := by rw [hsinv]
    _ = x⁻¹ := hsInvX

private lemma S_le_normalizer_and_inf_centralizer_eq_S0_local
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (hcomm : ⁅c.S0, c.U⁆ = ⊥)
    {s : G} (hs : c.IsReflection s) {I X : Subgroup G}
    (hI : IsInvertedSubgroup I c.U s) (hXne : X ≠ ⊥) (hXI : X ≤ I) :
    (c.S : Subgroup G) ≤ Subgroup.normalizer (X : Set G) ∧
      (c.S : Subgroup G) ⊓ Subgroup.centralizer (X : Set G) = c.S0 := by
  have hIleU : I ≤ c.U := by
    intro x hxI
    have hxInvSet : x ∈ invertedElements c.U s := by
      rw [← hI]
      exact hxI
    exact hxInvSet.1
  have hXU : X ≤ c.U := hXI.trans hIleU
  have hS0centU : c.S0 ≤ Subgroup.centralizer (c.U : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hcomm
  have hS0centX : c.S0 ≤ Subgroup.centralizer (X : Set G) :=
    hS0centU.trans (Subgroup.centralizer_le (SetLike.coe_mono hXU))
  have hSleN : (c.S : Subgroup G) ≤ Subgroup.normalizer (X : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro g hgS x hxX
    by_cases hgS0 : g ∈ c.S0
    · have hgcent : g ∈ Subgroup.centralizer (X : Set G) := hS0centX hgS0
      have hxcomm : x * g = g * x :=
        (Subgroup.mem_centralizer_iff.mp hgcent) x hxX
      rw [← hxcomm]
      simpa using hxX
    · have hginv : g * x * g⁻¹ = x⁻¹ :=
        reflection_inverts_subgroup_local c hcomm hs ⟨hgS, hgS0⟩ hI hXI x hxX
      rw [hginv]
      exact X.inv_mem hxX
  refine ⟨hSleN, le_antisymm ?_ ?_⟩
  · intro g hg
    by_contra hgS0
    have hgref : c.IsReflection g := ⟨hg.1, hgS0⟩
    apply hXne
    rw [Subgroup.eq_bot_iff_forall]
    intro x hxX
    have hginv : g * x * g⁻¹ = x⁻¹ :=
      reflection_inverts_subgroup_local c hcomm hs hgref hI hXI x hxX
    have hxcomm : x * g = g * x :=
      (Subgroup.mem_centralizer_iff.mp hg.2) x hxX
    have hgfix : g * x * g⁻¹ = x := by
      rw [← hxcomm]
      group
    have hxeq : x = x⁻¹ := hgfix.symm.trans hginv
    have hx2 : x ^ 2 = 1 := by
      rw [pow_two]
      calc
        x * x = x⁻¹ * x := congrArg (fun z : G => z * x) hxeq
        _ = 1 := by simp
    have hUcop : Nat.Coprime 2 (Nat.card c.U) := by
      change Nat.Coprime 2
        (Nat.card ((pPrimeCore 2 c.H).map c.H.subtype))
      rw [Subgroup.card_map_of_injective c.H.subtype_injective]
      exact pPrimeCore_coprime_card (p := 2) (G := c.H)
    have hXcop : Nat.Coprime 2 (Nat.card X) :=
      Nat.Coprime.of_dvd_right (Subgroup.card_dvd_of_le hXU) hUcop
    have hxSub2 : (⟨x, hxX⟩ : X) ^ 2 = 1 := by
      apply Subtype.ext
      exact hx2
    exact congrArg Subtype.val
      (eq_one_of_sq_eq_one_of_coprime_two (G := X) hXcop hxSub2)
  · exact le_inf c.S0_le_S hS0centX

private theorem cyclic_sylow_centralizer_subgroup_local
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) {X : Subgroup G}
    (hSleN : (c.S : Subgroup G) ≤ Subgroup.normalizer (X : Set G))
    (hInf : (c.S : Subgroup G) ⊓ Subgroup.centralizer (X : Set G) = c.S0) :
    ∀ P : Sylow 2
        (↥((Subgroup.centralizer (X : Set G)).subgroupOf
          (Subgroup.normalizer (X : Set G)))), IsCyclic P := by
  classical
  let N : Subgroup G := Subgroup.normalizer (X : Set G)
  let C : Subgroup N := (Subgroup.centralizer (X : Set G)).subgroupOf N
  let SN : Sylow 2 N := c.S.subtype hSleN
  let PC : Sylow 2 C :=
    BenderSuzuki.External.hallSylowSubgroupOfNormal SN C
  have hPCcyc : IsCyclic PC := by
    let : IsCyclic (↥c.S0) := c.S0_cyclic
    let f : (PC : Subgroup C) →* c.S0 :=
      { toFun := fun p => ⟨(p : G), by
          have hpPC : (p : C) ∈ (PC : Subgroup C) := p.2
          have hpComap : (p : C) ∈
              (SN : Subgroup N).comap C.subtype := by
            simpa [PC, BenderSuzuki.External.hallSylowSubgroupOfNormal_coe]
              using hpPC
          have hpS : (p : G) ∈ (c.S : Subgroup G) := by
            exact Subgroup.mem_subgroupOf.mp
              (show (p : N) ∈ (c.S : Subgroup G).subgroupOf N from hpComap)
          have hpC : (p : G) ∈ Subgroup.centralizer (X : Set G) :=
            Subgroup.mem_subgroupOf.mp (p : C).2
          rw [← hInf]
          exact ⟨hpS, hpC⟩⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    exact isCyclic_of_injective f (by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : c.S0 => (z : G)) hab)
  intro P
  exact (MulEquiv.isCyclic (Sylow.equiv P PC)).mpr hPCcyc

private theorem cyclic_sylow_normalizer_quotient_local
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) {X : Subgroup G}
    (hSleN : (c.S : Subgroup G) ≤ Subgroup.normalizer (X : Set G))
    (hInf : (c.S : Subgroup G) ⊓ Subgroup.centralizer (X : Set G) = c.S0) :
    ∀ P : Sylow 2
        ((↥(Subgroup.normalizer (X : Set G))) ⧸
          ((Subgroup.centralizer (X : Set G)).subgroupOf
            (Subgroup.normalizer (X : Set G)))), IsCyclic P := by
  classical
  let N : Subgroup G := Subgroup.normalizer (X : Set G)
  let C : Subgroup N := (Subgroup.centralizer (X : Set G)).subgroupOf N
  let : C.Normal :=
    Subgroup.normal_subgroupOf_centralizer_normalizer (X : Set G)
  let SN : Sylow 2 N := c.S.subtype hSleN
  let q : N →* N ⧸ C := QuotientGroup.mk' C
  let SQ : Sylow 2 (N ⧸ C) :=
    Sylow.mapSurjective (QuotientGroup.mk'_surjective C) SN
  have hSNmap : (SN : Subgroup N).map N.subtype = (c.S : Subgroup G) := by
    rw [show (SN : Subgroup N) =
      (c.S : Subgroup G).subgroupOf N by exact Sylow.coe_subtype c.S hSleN]
    exact Subgroup.map_subgroupOf_eq_of_le hSleN
  have hCmap : C.map N.subtype = Subgroup.centralizer (X : Set G) := by
    exact Subgroup.map_subgroupOf_eq_of_le
      (Subgroup.centralizer_le_normalizer (X : Set G))
  let K : Subgroup N := (SN : Subgroup N) ⊓ C
  have hKmap : K.map N.subtype = c.S0 := by
    dsimp [K]
    rw [Subgroup.map_inf _ _ _ N.subtype_injective, hSNmap, hCmap, hInf]
  have hcardK : Nat.card K = Nat.card c.S0 := by
    have hcard := Subgroup.card_map_of_injective
      (K := K) (f := N.subtype) N.subtype_injective
    rw [hKmap] at hcard
    exact hcard.symm
  have hcardSN : Nat.card (SN : Subgroup N) = Nat.card c.S := by
    rw [show (SN : Subgroup N) =
      (c.S : Subgroup G).subgroupOf N by exact Sylow.coe_subtype c.S hSleN]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSleN).toEquiv
  have hcardFormula := card_map_eq_card_mul_card_ker q (SN : Subgroup N)
  have hker : q.ker = C := QuotientGroup.ker_mk' C
  have hmap : (SN : Subgroup N).map q = (SQ : Subgroup (N ⧸ C)) := by
    exact (Sylow.coe_mapSurjective (QuotientGroup.mk'_surjective C) SN).symm
  have hcardSQ : Nat.card SQ = 2 := by
    rw [hcardSN, hmap, hker, show (SN : Subgroup N) ⊓ C = K by rfl,
      hcardK, c.S_index_two] at hcardFormula
    exact Nat.mul_right_cancel (Nat.card_pos (α := c.S0))
      (by simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hcardFormula.symm)
  have hSQcyc : IsCyclic SQ := isCyclic_of_prime_card hcardSQ
  intro P
  exact (MulEquiv.isCyclic (Sylow.equiv P SQ)).mpr hSQcyc

/-- A finite group with cyclic Sylow `2`-subgroups is solvable. -/
private theorem isSolvable_of_cyclic_sylow_two
    {G : Type u} [Group G] [Finite G]
    (hcyc : ∀ P : Sylow 2 G, IsCyclic P) :
    Group.IsSolvable G := by
  classical
  have hcomp : HasNormalPComplement 2 G := by
    by_cases h2 : 2 ∣ Nat.card G
    · let S : Sylow 2 G := Classical.choice Sylow.nonempty
      have hmin : (Nat.card G).minFac = 2 :=
        (Nat.minFac_eq_two_iff (Nat.card G)).2 h2
      have hNC : Subgroup.normalizer (S : Set G) ≤
          Subgroup.centralizer (S : Set G) :=
        (hcyc S).normalizer_le_centralizer hmin
      have hScenter : (S : Subgroup G) ≤
          centerIn (G := G) (Subgroup.normalizer (S : Set G)) := by
        intro s hs
        refine ⟨Subgroup.le_normalizer hs, ?_⟩
        change s ∈ Subgroup.centralizer
          (Subgroup.normalizer (S : Set G) : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro g hg
        exact (Subgroup.mem_centralizer_iff.mp (hNC hg) s hs).symm
      exact hasNormalPComplement_of_sylow_le_center_normalizer
        (G := G) 2 S hScenter
    · have hodd : Odd (Nat.card G) := by
        rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
        exact h2
      refine ⟨⊤, inferInstance, ?_, ?_⟩
      · simpa using hodd.coprime_two_left
      · intro x
        refine ⟨0, ?_⟩
        have hsub : Subsingleton (G ⧸ (⊤ : Subgroup G)) :=
          QuotientGroup.subsingleton_quotient_top
        simpa using (@Subsingleton.elim _ hsub x 1)
  rcases hcomp with ⟨K, hKnormal, hKcop, hQp⟩
  let : K.Normal := hKnormal
  have hKodd : Odd (Nat.card K) := Nat.coprime_two_left.mp hKcop
  have hKsolv : Group.IsSolvable K := odd_order_theorem K hKodd
  have hQsolv : Group.IsSolvable (G ⧸ K) := isSolvable_of_isPGroup hQp
  exact isSolvable_of_normal_solvable_quotient_solvable K hKsolv hQsolv

private theorem normalizer_isSolvable_local
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) {X : Subgroup G}
    (hSleN : (c.S : Subgroup G) ≤ Subgroup.normalizer (X : Set G))
    (hInf : (c.S : Subgroup G) ⊓ Subgroup.centralizer (X : Set G) = c.S0) :
    Group.IsSolvable (Subgroup.normalizer (X : Set G)) := by
  let N : Subgroup G := Subgroup.normalizer (X : Set G)
  let C : Subgroup N := (Subgroup.centralizer (X : Set G)).subgroupOf N
  let : C.Normal :=
    Subgroup.normal_subgroupOf_centralizer_normalizer (X : Set G)
  have hCsolv : Group.IsSolvable C :=
    isSolvable_of_cyclic_sylow_two
      (cyclic_sylow_centralizer_subgroup_local c hSleN hInf)
  have hQsolv : Group.IsSolvable (N ⧸ C) :=
    isSolvable_of_cyclic_sylow_two
      (cyclic_sylow_normalizer_quotient_local c hSleN hInf)
  exact isSolvable_of_normal_solvable_quotient_solvable C hCsolv hQsolv

private theorem oddCoreOf_isNormalIn_local {G : Type u} [Group G]
    (H : Subgroup G) : IsNormalIn (oddCoreOf H) H := by
  refine ⟨?_, ?_⟩
  · intro x hx
    rcases (Subgroup.mem_map).1 hx with ⟨y, _hy, rfl⟩
    exact y.2
  · intro h hh x hx
    rcases (Subgroup.mem_map).1 hx with ⟨y, hy, rfl⟩
    refine Subgroup.mem_map.mpr
      ⟨(⟨h, hh⟩ : ↥H) * y * (⟨h, hh⟩ : ↥H)⁻¹, ?_, by simp⟩
    exact (pPrimeCore_normal (p := 2) (G := ↥H)).conj_mem
      y hy (⟨h, hh⟩ : ↥H)

private theorem FU_le_fittingSubgroupOf_Hhat_local
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (h26 : CentralizerStructure c) :
    c.FU ≤ fittingSubgroupOf c.Hhat := by
  have hUnorm : IsNormalIn c.U c.Hhat := by
    rw [h26.1]
    exact oddCoreOf_isNormalIn_local c.Hhat
  have hFUnorm : IsNormalIn c.FU c.Hhat := by
    have h := fstar_characteristic_subgroupOf_map_normal_in
      (A := c.Hhat) (F := c.U) (K := fittingSubgroup (↥c.U))
      fittingSubgroup_characteristic hUnorm
    change IsNormalIn ((fittingSubgroup (↥c.U)).map c.U.subtype) c.Hhat
    exact h
  have hFUnil : Group.IsNilpotent (↥c.FU) := by
    change Group.IsNilpotent (↥(fittingSubgroupOf c.U))
    exact fittingSubgroupOf_isNilpotent c.U
  apply le_fittingSubgroupOf_of_isNormalIn_nilpotent hFUnorm.1 hFUnorm
  exact hFUnil

private theorem exists_escaping_inverted_normalizer_local
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G) (c : CentralizerSetup G)
    (hinverted : ∀ s : G, c.IsReflection s →
      ∃ I : Subgroup G, IsInvertedSubgroup I c.U s)
    (hcomm : ⁅c.S0, c.U⁆ = ⊥) :
    ∃ s I X,
      c.IsReflection s ∧ IsInvertedSubgroup I c.U s ∧
        X ≠ ⊥ ∧ X ≤ I ∧
          ¬ Subgroup.normalizer (X : Set G) ≤ c.H := by
  have hcent : Centralizes c.S0 c.U :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hcomm
  by_contra hnone
  push Not at hnone
  apply (lemma_2_2 hmin c).1
  refine ⟨hcent, ?_⟩
  intro s hs
  rcases hinverted s hs with ⟨I, hI⟩
  refine ⟨I, hI,
    (centralizerSetup_reflection_invertedSubgroup_abelian_normal c hs hI).2.1,
    ?_⟩
  intro X hXne hXI
  exact hnone s I X hs hI hXne hXI

private theorem inverted_normalizer_ne_top_local
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G) (c : CentralizerSetup G)
    {X : Subgroup G} (hXne : X ≠ ⊥) (hXU : X ≤ c.U) :
    Subgroup.normalizer (X : Set G) ≠ ⊤ := by
  intro hNtop
  have hXnormal : X.Normal :=
    (Subgroup.normalizer_eq_top_iff (H := X)).mp hNtop
  rcases (haveI := hXnormal; (minimalCounterexample_isSimple hmin).eq_bot_or_eq_top_of_normal
      X) with hXbot | hXtop
  · exact hXne hXbot
  · have hUleH : c.U ≤ c.H :=
      Subgroup.map_subtype_le (H := c.H) (pPrimeCore 2 c.H)
    have hXHhat : X ≤ c.Hhat := hXU.trans (hUleH.trans c.H_le_Hhat)
    have htop_le : (⊤ : Subgroup G) ≤ c.Hhat := by
      simpa [hXtop] using hXHhat
    exact c.Hhat_maximal.ne_top (top_unique htop_le)

private theorem exists_component_of_componentLayerOf_ne_bot_local
    {G : Type u} [Group G]
    (N : Subgroup G) (hE : componentLayerOf N ≠ ⊥) :
    ∃ E : Subgroup G, IsComponentOf E N := by
  by_cases hex : ∃ E : Subgroup G, IsComponentOf E N
  · exact hex
  · exfalso
    apply hE
    rw [componentLayerOf]
    apply le_antisymm
    · refine sSup_le (fun E hcomp => ?_)
      have hEbot : E = ⊥ := by
        by_contra hne
        exact hex ⟨E, hcomp⟩
      rw [hEbot]
    · exact bot_le

/-- First assertion of Lemma 2.8.  Under `[S₀,U]=1`, Theorem 2.6 forces
`Ĥ = H`; Lemma 2.2 then supplies `1 ≠ X ≤ I_U(s)` whose normalizer escapes
`Ĥ`.  That normalizer is controlled, contains `S`, and is solvable, whereas
the Lemma 2.7 consequence forces it to have a nontrivial component. -/
private theorem lemma_2_8_commutator_S0_ne_bot {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hinverted : ∀ s : G, c.IsReflection s →
      ∃ I : Subgroup G, IsInvertedSubgroup I c.U s) :
    ⁅c.S0, c.U⁆ ≠ ⊥ := by
  intro hcomm
  have h26 := theorem_2_6 hmin c
  have hHhat : c.Hhat = c.H :=
    hhat_eq_H_of_commutator_eq_bot hmin c h26 hcomm
  rcases exists_escaping_inverted_normalizer_local hmin c hinverted hcomm with
    ⟨s, I, X, hs, hI, hXne, hXI, hnotH⟩
  have hIleU : I ≤ c.U := by
    intro x hxI
    have hxInvSet : x ∈ invertedElements c.U s := by
      rw [← hI]
      exact hxI
    exact hxInvSet.1
  have hXU : X ≤ c.U := hXI.trans hIleU
  let N : Subgroup G := Subgroup.normalizer (X : Set G)
  have hSN :=
    S_le_normalizer_and_inf_centralizer_eq_S0_local
      c hcomm hs hI hXne hXI
  have hSleN : (c.S : Subgroup G) ≤ N := by
    simpa [N] using hSN.1
  have hInf :
      (c.S : Subgroup G) ⊓ Subgroup.centralizer (X : Set G) = c.S0 :=
    hSN.2
  have hNproper : N ≠ ⊤ := by
    simpa [N] using inverted_normalizer_ne_top_local hmin c hXne hXU
  have hnotHhat : ¬ N ≤ c.Hhat := by
    simpa [N, hHhat] using hnotH
  have hXleFU : X ≤ c.FU :=
    hXI.trans
      (centralizerSetup_reflection_invertedSubgroup_abelian_normal c hs hI).2.2
  have hcontrol : NormalizerControlledBy c.Hhat N := by
    refine ⟨X, hXne, hXleFU.trans
      (FU_le_fittingSubgroupOf_Hhat_local c h26), ?_⟩
    exact le_rfl
  have htN : c.t ∈ componentLayerOf N := by
    by_contra htnot
    have hSylow : ∀ P : Sylow 2 (↥N), ¬ IsCyclic P :=
      sylow_noncyclic_of_S_le c N hSleN
    exact
      (lemma_2_7_consequence_local
        hmin c N hNproper hcontrol hnotHhat htnot hSleN hSylow)
        (lemma_2_8_commutator_le_FU c hinverted)
  have hLayer : componentLayerOf N ≠ ⊥ := by
    intro hbot
    have htbot : c.t ∈ (⊥ : Subgroup G) := by
      simpa [hbot] using htN
    exact c.t_involution.1 (Subgroup.mem_bot.mp htbot)
  obtain ⟨E, hE⟩ :=
    exists_component_of_componentLayerOf_ne_bot_local N hLayer
  have hNsolv : Group.IsSolvable (Subgroup.normalizer (X : Set G)) :=
    normalizer_isSolvable_local c hSleN hInf
  let : Group.IsSolvable N := by
    change Group.IsSolvable (Subgroup.normalizer (X : Set G))
    exact hNsolv
  let : Group.IsSolvable (E.subgroupOf N) := inferInstance
  have hEsolv : Group.IsSolvable E :=
    isSolvable_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hE.1)
  let : Nontrivial E := hE.2.2.1
  let : Group.IsPerfect E :=
    ⟨by simpa [derivedSubgroup] using hE.2.2.2.1⟩
  exact Group.IsPerfect.not_isSolvable E hEsolv

/-! ## Lemma 2.8 -/

/-- Second assertion of Lemma 2.8: every controlled proper subgroup `M` not
contained in `Ĥ` and containing `S` has `t ∈ E(M)`.  The proof is the contrapositive:
assuming `t ∉ E(M)`, the specialized Lemma 2.7 consequence gives
`¬ [S, U] ≤ F(U)`, contradicting the proved commutator transfer. -/
private theorem lemma_2_8_second_assertion {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hinverted : ∀ s : G, c.IsReflection s →
      ∃ I : Subgroup G, IsInvertedSubgroup I c.U s) :
    ∀ M : Subgroup G,
      M ≠ ⊤ →
        NormalizerControlledBy c.Hhat M →
          (¬ M ≤ c.Hhat) →
            (c.S : Subgroup G) ≤ M → c.t ∈ componentLayerOf M := by
  intro M hMproper hN hnotle hSle
  by_contra htnot
  have hSylow : ∀ P : Sylow 2 (↥M), ¬ IsCyclic P :=
    sylow_noncyclic_of_S_le c M hSle
  have h27 := lemma_2_7_consequence_local
    hmin c M hMproper hN hnotle htnot hSle hSylow
  exact h27 (lemma_2_8_commutator_le_FU c hinverted)

/-- Lemma 2.8 (Bender, *Finite Groups with Dihedral Sylow 2-Subgroups*,
p. 221): if every reflection-inverted set is a subgroup, then
`[S0, U] ≠ 1` and every controlled proper `M ⊄ Ĥ` containing `S` has
`t ∈ E(M)`.  The second assertion is assembled here from the
proved Lemma 2.7 consequence and the commutator transfer; the first assertion
uses the escaping-normalizer and solvability contradiction above. -/
public theorem lemma_2_8
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hinverted : ∀ s : G, c.IsReflection s →
      ∃ I : Subgroup G, IsInvertedSubgroup I c.U s) :
    ⁅c.S0, c.U⁆ ≠ ⊥ ∧
      ∀ M : Subgroup G,
        M ≠ ⊤ →
          NormalizerControlledBy c.Hhat M →
            (¬ M ≤ c.Hhat) →
              (c.S : Subgroup G) ≤ M → c.t ∈ componentLayerOf M := by
  exact ⟨lemma_2_8_commutator_S0_ne_bot hmin c hinverted,
    lemma_2_8_second_assertion hmin c hinverted⟩

end CFSG.GorensteinWalter
