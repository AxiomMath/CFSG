module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Suzuki.VI.theorem_2_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.V.theorem_8_14
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import Mathlib.GroupTheory.PGroup
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.lemma_3_1

namespace CFSG
end CFSG
open CFSG

/-!
# Point-stabilizer Frobenius kernels for Huppert--Blackburn XI

This file formalizes the standing Frobenius kernel used in the proof of
XI.11.16.  For a Zassenhaus action, a point stabilizer acts as a Frobenius
group on the complement of that point.
-/

namespace CFSG.BenderSuzuki
namespace External

public theorem huppert_blackburn_XI_regular_of_isComplement_stabilizer
    {G Omega : Type*} [Group G] [MulAction G Omega]
    {K : Subgroup G} {a : Omega}
    (hcomp : K.IsComplement' (MulAction.stabilizer G a))
    (htrans : MulAction.IsPretransitive G Omega) :
    ∀ x y : Omega, ∃! k : K, (k : G) • x = y := by
  letI : MulAction.IsPretransitive G Omega := htrans
  have hbase : ∀ x : Omega, ∃! k : K, (k : G) • a = x := by
    intro x
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G a x
    obtain ⟨kr, hkr, _⟩ := hcomp.existsUnique g
    have hkrbase : (kr.1 : G) • a = x := by
      rw [← hg, ← hkr]
      simp only [mul_smul]
      rw [MulAction.mem_stabilizer_iff.mp kr.2.property]
    refine ⟨kr.1, hkrbase, ?_⟩
    intro k hk
    have hfix : ((↑((kr.1 : K)⁻¹ * k) : G)) • a = a := by
      change ((kr.1 : G)⁻¹ * (k : G)) • a = a
      rw [mul_smul, hk, ← hkrbase, inv_smul_smul]
    have hmemR : ((↑((kr.1 : K)⁻¹ * k) : G)) ∈
        MulAction.stabilizer G a :=
      MulAction.mem_stabilizer_iff.mpr hfix
    have hone : ((↑((kr.1 : K)⁻¹ * k) : G)) = 1 :=
      Subgroup.disjoint_def.mp hcomp.disjoint
        (((kr.1 : K)⁻¹ * k).property) hmemR
    exact (Subtype.ext (inv_mul_eq_one.mp hone)).symm
  intro x y
  obtain ⟨kx, hkx, _⟩ := hbase x
  obtain ⟨ky, hky, hky_unique⟩ := hbase y
  refine ⟨ky * kx⁻¹, ?_, ?_⟩
  · change ((ky : G) * (kx : G)⁻¹) • x = y
    rw [mul_smul, ← hkx, inv_smul_smul, hky]
  · intro k hk
    have hbase_y : ((k * kx : K) : G) • a = y := by
      change ((k : G) * (kx : G)) • a = y
      rw [mul_smul, hkx, hk]
    have heq : k * kx = ky := hky_unique (k * kx) hbase_y
    calc
      k = (k * kx) * kx⁻¹ := by simp
      _ = ky * kx⁻¹ := by rw [heq]

private theorem huppert_blackburn_XI_twoPointStabilizer_ne_bot
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    [FaithfulSMul G Omega] [Finite Omega]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (hno_regular_normal :
      ¬ ∃ R : Subgroup G, R.Normal ∧ R ≠ ⊥ ∧
        ∀ x y : Omega, ∃! r : R, (r : G) • x = y)
    (a b : Omega) (hab : a ≠ b) :
    let b' : SubMulAction.ofStabilizer G a := ⟨b, hab.symm⟩
    MulAction.stabilizer (MulAction.stabilizer G a) b' ≠ ⊥ := by
  letI : MulAction.IsMultiplyPretransitive G Omega 2 := htwo
  letI : MulAction.IsPretransitive G Omega :=
    MulAction.isPretransitive_of_is_two_pretransitive
  let R := MulAction.stabilizer G a
  let b' : SubMulAction.ofStabilizer G a := ⟨b, hab.symm⟩
  let D := MulAction.stabilizer R b'
  change D ≠ ⊥
  intro hDbot
  have hpair_fix_eq_one {c : Omega} (hc : c ≠ a) (x : G)
      (hxa : x • a = a) (hxc : x • c = c) : x = 1 := by
    obtain ⟨g, hga, hgb⟩ :=
      MulAction.is_two_pretransitive_iff.mp htwo hab hc.symm
    let gR : R := ⟨g, hga⟩
    let xR : R := ⟨x, hxa⟩
    have hfixb : ((gR⁻¹ * xR * gR : R) • b') = b' := by
      apply Subtype.ext
      change (g⁻¹ * x * g) • b = b
      rw [mul_smul, mul_smul, hgb, hxc, ← hgb, inv_smul_smul]
    have hzmem : gR⁻¹ * xR * gR ∈ D :=
      MulAction.mem_stabilizer_iff.mpr hfixb
    have hzone : gR⁻¹ * xR * gR = 1 := by
      have : gR⁻¹ * xR * gR ∈ (⊥ : Subgroup R) := hDbot ▸ hzmem
      simpa using this
    have hxRone : xR = 1 := by
      have hz := congrArg (fun z : R => gR * z * gR⁻¹) hzone
      simpa [mul_assoc] using hz
    exact congrArg (fun z : R => (z : G)) hxRone
  have hR_TI : ∀ g : G, g ∉ R → Disjoint R (R.conjBy g) := by
    intro g hg
    rw [Subgroup.disjoint_def]
    intro x hxR hxconj
    apply hpair_fix_eq_one (c := g • a)
    · intro hga
      apply hg
      exact MulAction.mem_stabilizer_iff.mpr hga
    · exact MulAction.mem_stabilizer_iff.mp hxR
    · rw [Subgroup.conjBy, Subgroup.mem_map] at hxconj
      rcases hxconj with ⟨r, hr, hrx⟩
      rw [← hrx]
      change (g * r * g⁻¹) • (g • a) = g • a
      rw [mul_smul, mul_smul, inv_smul_smul,
        MulAction.mem_stabilizer_iff.mp hr]
  have hRne : R ≠ ⊥ := by
    intro hRbot
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G a b
    have hg_ne : g ≠ 1 := by
      intro hgone
      apply hab
      simpa [hgone] using hg
    have htop_ne : (⊤ : Subgroup G) ≠ ⊥ := by
      intro htop
      have hg_bot : g ∈ (⊥ : Subgroup G) :=
        htop ▸ (show g ∈ (⊤ : Subgroup G) by simp)
      exact hg_ne (by simpa using hg_bot)
    apply hno_regular_normal
    refine ⟨⊤, Subgroup.normal_top, htop_ne, ?_⟩
    have hcompTop : (⊤ : Subgroup G).IsComplement' R := by
      rw [hRbot]
      exact Subgroup.isComplement'_top_bot
    exact huppert_blackburn_XI_regular_of_isComplement_stabilizer
      (a := a) hcompTop
      (MulAction.isPretransitive_of_is_two_pretransitive (G := G) (α := Omega))
  have hRproper : R ≠ ⊤ := by
    intro hRtop
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G a b
    have hgR : g ∈ R := by rw [hRtop]; simp
    have hga : g • a = a := MulAction.mem_stabilizer_iff.mp hgR
    exact hab (hga.symm.trans hg)
  obtain ⟨K, hfrob⟩ :=
    Suzuki.VI.suzuki_ch6_theorem_2_3 R hRne hRproper hR_TI
  apply hno_regular_normal
  refine ⟨K, hfrob.normal, hfrob.kernel_ne_bot, ?_⟩
  exact huppert_blackburn_XI_regular_of_isComplement_stabilizer
    (a := a) hfrob.isComplement'
    (MulAction.isPretransitive_of_is_two_pretransitive (G := G) (α := Omega))

/-- The Frobenius kernel of a point stabilizer in the Zassenhaus action used
throughout Huppert--Blackburn XI. -/
public theorem huppert_blackburn_XI_pointStabilizer_frobeniusKernel_exists
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    [FaithfulSMul G Omega] [Finite Omega]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (hat_most_two_fixed_points :
      ∀ g : G, g ≠ 1 →
        ∀ x y z : Omega,
          x ≠ y → x ≠ z → y ≠ z →
          ¬ (g • x = x ∧ g • y = y ∧ g • z = z))
    (hno_regular_normal :
      ¬ ∃ R : Subgroup G, R.Normal ∧ R ≠ ⊥ ∧
        ∀ x y : Omega, ∃! r : R, (r : G) • x = y)
    (a b : Omega) (hab : a ≠ b) :
    let b' : SubMulAction.ofStabilizer G a := ⟨b, hab.symm⟩
    ∃ F : Subgroup (MulAction.stabilizer G a),
      IsFrobeniusGroupWithKernelComplement F
        (MulAction.stabilizer (MulAction.stabilizer G a) b') := by
  letI : MulAction.IsMultiplyPretransitive G Omega 2 := htwo
  letI : MulAction.IsPretransitive G Omega :=
    MulAction.isPretransitive_of_is_two_pretransitive
  let H := MulAction.stabilizer G a
  let X := SubMulAction.ofStabilizer G a
  let b' : X := ⟨b, hab.symm⟩
  let D := MulAction.stabilizer H b'
  change ∃ F : Subgroup H, IsFrobeniusGroupWithKernelComplement F D
  have hDne : D ≠ ⊥ :=
    huppert_blackburn_XI_twoPointStabilizer_ne_bot
      htwo hno_regular_normal a b hab
  have hstab_multi : MulAction.IsMultiplyPretransitive H X 1 :=
    (SubMulAction.ofStabilizer.isMultiplyPretransitive
      (G := G) (a := a)).mp htwo
  letI : MulAction.IsPretransitive H X :=
    (MulAction.is_one_pretransitive_iff (G := H) (α := X)).mp hstab_multi
  have hDproper : D ≠ ⊤ := by
    intro hDtop
    letI : Nontrivial D := (Subgroup.nontrivial_iff_ne_bot D).2 hDne
    obtain ⟨d, hdne⟩ := exists_ne (1 : D)
    have hdfix_all (c : Omega) : ((d : H) : G) • c = c := by
      by_cases hca : c = a
      · subst c
        exact (d : H).property
      · let c' : X := ⟨c, hca⟩
        obtain ⟨h, hh⟩ := MulAction.exists_smul_eq H b' c'
        have hhD : h ∈ D := by rw [hDtop]; simp
        have hhfix : h • b' = b' := MulAction.mem_stabilizer_iff.mp hhD
        have hc'b' : c' = b' := hh.symm.trans hhfix
        have hcb : c = b := congrArg Subtype.val hc'b'
        subst c
        exact congrArg Subtype.val
          (MulAction.mem_stabilizer_iff.mp d.property)
    have hdG : ((d : H) : G) = 1 := by
      apply eq_of_smul_eq_smul (α := Omega)
      intro c
      simpa using hdfix_all c
    apply hdne
    apply Subtype.ext
    apply Subtype.ext
    exact hdG
  have hD_TI : ∀ h : H, h ∉ D → Disjoint D (D.conjBy h) := by
    intro h hhD
    rw [Subgroup.disjoint_def]
    intro x hxD hxconj
    have hxb' : x • b' = b' := MulAction.mem_stabilizer_iff.mp hxD
    have hhc_ne : (h • b' : X) ≠ b' := by
      intro heq
      apply hhD
      exact MulAction.mem_stabilizer_iff.mpr heq
    have hxc : x • (h • b') = h • b' := by
      rw [Subgroup.conjBy, Subgroup.mem_map] at hxconj
      rcases hxconj with ⟨r, hrD, hrx⟩
      rw [← hrx]
      change (h * r * h⁻¹) • (h • b') = h • b'
      rw [mul_smul, mul_smul, inv_smul_smul,
        MulAction.mem_stabilizer_iff.mp hrD]
    by_contra hxne
    have hxGne : ((x : H) : G) ≠ 1 := by
      intro hxone
      apply hxne
      apply Subtype.ext
      exact hxone
    apply hat_most_two_fixed_points ((x : H) : G) hxGne
        a b ((h • b' : X) : Omega) hab
    · exact Ne.symm (h • b').property
    · exact fun hbc => hhc_ne (Subtype.ext hbc.symm)
    refine ⟨(x : H).property, ?_, ?_⟩
    · exact congrArg Subtype.val hxb'
    · exact congrArg Subtype.val hxc
  exact Suzuki.VI.suzuki_ch6_theorem_2_3 D hDne hDproper hD_TI

/-- A finite Frobenius kernel is nilpotent.  This is the Thompson
fixed-point-free automorphism step used before the XI.6 classification. -/
public theorem huppert_blackburn_XI_frobeniusKernel_nilpotent
    {H : Type*} [Group H] [Finite H]
    (F D : Subgroup H)
    (hFrob : IsFrobeniusGroupWithKernelComplement F D) :
    Group.IsNilpotent F := by
  letI : F.Normal := hFrob.normal
  apply
    huppert_V_8_14_thompson_fixedPointFree_conjugation_nilpotent_subgroup
      (G := H) F D
  · exact Subgroup.le_normalizer_of_normal
  · letI : Nontrivial D :=
      (Subgroup.nontrivial_iff_ne_bot D).mpr hFrob.complement_ne_bot
    obtain ⟨d, hd⟩ := exists_ne (1 : D)
    exact ⟨d, d.property, fun h => hd (Subtype.ext h)⟩
  · intro x hxD hxne
    let d : D := ⟨x, hxD⟩
    have hdne : d ≠ 1 := fun h => hxne (congrArg Subtype.val h)
    have hcent :=
      (lemma_3_1 F D hFrob.kernel_ne_bot hFrob.complement_ne_bot
        hFrob.normal hFrob.isComplement').mp hFrob d hdne
    simpa [elementCentralizerIn, inf_comm] using hcent

set_option backward.isDefEq.respectTransparency false in
/-- The regular Frobenius kernel identifies with the complement of the fixed
point.  The equivalence sends a kernel element to its translate of the second
distinguished point. -/
public theorem huppert_blackburn_XI_pointStabilizer_exists_kernelPointEquiv
    {G Omega : Type*} [Group G] [MulAction G Omega]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob :
      IsFrobeniusGroupWithKernelComplement F
        (MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a))) :
    ∃ e : F ≃ SubMulAction.ofStabilizer G a,
      ∀ f : F,
        e f =
          (f : MulAction.stabilizer G a) •
            (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a) := by
  letI : MulAction.IsMultiplyPretransitive G Omega 2 := htwo
  letI : MulAction.IsPretransitive G Omega :=
    MulAction.isPretransitive_of_is_two_pretransitive
  let H := MulAction.stabilizer G a
  let X := SubMulAction.ofStabilizer G a
  let b' : X := ⟨b, hab.symm⟩
  let D := MulAction.stabilizer H b'
  change IsFrobeniusGroupWithKernelComplement F D at hFrob
  have hstab_multi : MulAction.IsMultiplyPretransitive H X 1 :=
    (SubMulAction.ofStabilizer.isMultiplyPretransitive
      (G := G) (a := a)).mp htwo
  letI : MulAction.IsPretransitive H X :=
    (MulAction.is_one_pretransitive_iff (G := H) (α := X)).mp hstab_multi
  have hregular : ∀ x y : X, ∃! f : F, (f : H) • x = y :=
    huppert_blackburn_XI_regular_of_isComplement_stabilizer
      hFrob.isComplement' (inferInstance : MulAction.IsPretransitive H X)
  let e : F ≃ X :=
    Equiv.ofBijective (fun f : F => (f : H) • b') (by
      constructor
      · intro x y hxy
        obtain ⟨k, _hk, huniq⟩ := hregular b' ((x : H) • b')
        have hxk : x = k := huniq x rfl
        have hyk : y = k := huniq y hxy.symm
        exact hxk.trans hyk.symm
      · intro y
        obtain ⟨f, hf, _⟩ := hregular b' y
        exact ⟨f, hf⟩)
  exact ⟨e, fun _ => rfl⟩


set_option backward.isDefEq.respectTransparency false in
/-- A point-stabilizer Frobenius kernel complementary to the two-point
stabilizer has cardinality equal to the degree minus one. -/
public theorem huppert_blackburn_XI_pointStabilizer_frobeniusKernel_card
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    [Fintype Omega]
    (n : ℕ) (hdegree : Fintype.card Omega = n + 1)
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob :
      IsFrobeniusGroupWithKernelComplement F
        (MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a))) :
    Nat.card F = n := by
  classical
  obtain ⟨kernelPointEquiv, _happly⟩ :=
    huppert_blackburn_XI_pointStabilizer_exists_kernelPointEquiv
      htwo a b hab F hFrob
  calc
    Nat.card F = Nat.card (SubMulAction.ofStabilizer G a) :=
      Nat.card_congr kernelPointEquiv
    _ = Nat.card Omega - 1 := SubMulAction.nat_card_ofStabilizer_eq G a
    _ = n := by simp [Nat.card_eq_fintype_card, hdegree]

set_option backward.isDefEq.respectTransparency false in
/-- Sharp triple transitivity makes the two-point stabilizer act regularly by
conjugation on the nonidentity elements of the point-stabilizer Frobenius
kernel. -/
public theorem huppert_blackburn_XI_sharpTriple_kernel_conj_regular
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    [Fintype Omega]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (hsharp :
      ∀ a b c a' b' c' : Omega,
        a ≠ b → a ≠ c → b ≠ c →
        a' ≠ b' → a' ≠ c' → b' ≠ c' →
        ∃! g : G,
          g • a = a' ∧ g • b = b' ∧ g • c = c')
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob :
      IsFrobeniusGroupWithKernelComplement F
        (MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a))) :
    ∀ x y : F, x ≠ 1 → y ≠ 1 →
      ∃! d : MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a),
        (d : MulAction.stabilizer G a) *
            (x : MulAction.stabilizer G a) *
            (d : MulAction.stabilizer G a)⁻¹ =
          (y : MulAction.stabilizer G a) := by
  classical
  let H := MulAction.stabilizer G a
  let X := SubMulAction.ofStabilizer G a
  let b' : X := ⟨b, hab.symm⟩
  let D := MulAction.stabilizer H b'
  change IsFrobeniusGroupWithKernelComplement F D at hFrob
  obtain ⟨kernelPointEquiv, _happly⟩ :=
    huppert_blackburn_XI_pointStabilizer_exists_kernelPointEquiv
      htwo a b hab F hFrob
  have hnot_fix_b' (x : F) (hx : x ≠ 1) : (x : H) • b' ≠ b' := by
    intro hfix
    have hxD : (x : H) ∈ D := MulAction.mem_stabilizer_iff.mpr hfix
    have hxbot : (x : H) ∈ (⊥ : Subgroup H) :=
      hFrob.isComplement'.disjoint.le_bot ⟨x.property, hxD⟩
    apply hx
    exact Subtype.ext (Subgroup.mem_bot.mp hxbot)
  intro x y hx hy
  let c : X := (x : H) • b'
  let e : X := (y : H) • b'
  have hcb' : c ≠ b' := hnot_fix_b' x hx
  have heb' : e ≠ b' := hnot_fix_b' y hy
  have hbc : b ≠ (c : Omega) := by
    intro hbc
    exact hcb' (Subtype.ext hbc.symm)
  have hbe : b ≠ (e : Omega) := by
    intro hbe
    exact heb' (Subtype.ext hbe.symm)
  have hac : a ≠ (c : Omega) := by
    intro hac
    apply c.property
    simp [hac]
  have hae : a ≠ (e : Omega) := by
    intro hae
    apply e.property
    simp [hae]
  obtain ⟨g, hg, huniq⟩ :=
    hsharp a b (c : Omega) a b (e : Omega)
      hab hac hbc hab hae hbe
  rcases hg with ⟨hga, hgb, hgc⟩
  let gH : H := ⟨g, hga⟩
  let gD : D :=
    ⟨gH, MulAction.mem_stabilizer_iff.mpr (Subtype.ext hgb)⟩
  let xconj : F :=
    ⟨(gD : H) * (x : H) * (gD : H)⁻¹,
      hFrob.normal.conj_mem (x : H) x.property (gD : H)⟩
  have hxconj_eq : xconj = y := kernelPointEquiv.injective (by
    rw [_happly xconj, _happly y]
    apply Subtype.ext
    change (g * ((x : H) : G) * g⁻¹) • b = ((y : H) : G) • b
    rw [mul_smul, mul_smul]
    have hginvb : g⁻¹ • b = b := by
      calc
        g⁻¹ • b = g⁻¹ • (g • b) := congrArg (fun z => g⁻¹ • z) hgb.symm
        _ = b := inv_smul_smul g b
    rw [hginvb]
    exact hgc)
  have hgD_conj :
      (gD : H) * (x : H) * (gD : H)⁻¹ = (y : H) :=
    congrArg Subtype.val hxconj_eq
  refine ⟨gD, hgD_conj, ?_⟩
  intro d hd
  have hdb' : (d : H) • b' = b' :=
    MulAction.mem_stabilizer_iff.mp d.property
  have hdb : (((d : H) : G) • b) = b := congrArg Subtype.val hdb'
  have hdsemi : (d : H) * (x : H) = (y : H) * (d : H) := by
    calc
      (d : H) * (x : H) =
          ((d : H) * (x : H) * (d : H)⁻¹) * (d : H) := by group
      _ = (y : H) * (d : H) := by rw [hd]
  have hdc : (((d : H) : G) • (c : Omega)) = (e : Omega) := by
    dsimp [c, e]
    change ((d : H) : G) • (((x : H) : G) • b) = ((y : H) : G) • b
    have hdsemiG :
        ((d : H) : G) * ((x : H) : G) =
          ((y : H) : G) * ((d : H) : G) := by
      simpa using congrArg Subtype.val hdsemi
    rw [← mul_smul, hdsemiG, mul_smul, hdb]
  apply Subtype.ext
  apply Subtype.ext
  exact huniq ((d : H) : G) ⟨(d : H).property, hdb, hdc⟩

set_option backward.isDefEq.respectTransparency false in
/-- In the sharply triply transitive branch, conjugation of a fixed
nonidentity kernel element gives coordinates from the two-point stabilizer to
the punctured Frobenius kernel. -/
public theorem huppert_blackburn_XI_twoPointStabilizer_exists_conjEquiv
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    [Fintype Omega]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (hsharp :
      ∀ a b c a' b' c' : Omega,
        a ≠ b → a ≠ c → b ≠ c →
        a' ≠ b' → a' ≠ c' → b' ≠ c' →
        ∃! g : G,
          g • a = a' ∧ g • b = b' ∧ g • c = c')
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob :
      IsFrobeniusGroupWithKernelComplement F
        (MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a))) :
    ∃ z : F, z ≠ 1 ∧
      ∃ e :
          MulAction.stabilizer (MulAction.stabilizer G a)
              (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a) ≃
            {x : F // x ≠ 1},
        ∀ d : MulAction.stabilizer (MulAction.stabilizer G a)
            (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a),
          ((e d).1 : MulAction.stabilizer G a) =
            (d : MulAction.stabilizer G a) *
              (z : MulAction.stabilizer G a) *
              (d : MulAction.stabilizer G a)⁻¹ := by
  classical
  let H := MulAction.stabilizer G a
  let X := SubMulAction.ofStabilizer G a
  let b' : X := ⟨b, hab.symm⟩
  let D := MulAction.stabilizer H b'
  change IsFrobeniusGroupWithKernelComplement F D at hFrob
  letI : Nontrivial F :=
    (Subgroup.nontrivial_iff_ne_bot F).2 hFrob.kernel_ne_bot
  obtain ⟨z, hz⟩ := exists_ne (1 : F)
  let image (d : D) : F :=
    ⟨(d : H) * (z : H) * (d : H)⁻¹,
      hFrob.normal.conj_mem (z : H) z.property (d : H)⟩
  have himage_ne (d : D) : image d ≠ 1 := by
    intro hi
    apply hz
    apply Subtype.ext
    have hiH : (image d : H) = 1 := congrArg Subtype.val hi
    change (d : H) * (z : H) * (d : H)⁻¹ = 1 at hiH
    calc
      (z : H) = (d : H)⁻¹ *
          ((d : H) * (z : H) * (d : H)⁻¹) * (d : H) := by group
      _ = 1 := by rw [hiH]; simp
  let phi : D → {x : F // x ≠ 1} := fun d => ⟨image d, himage_ne d⟩
  have hphi : Function.Bijective phi := by
    constructor
    · intro d e hde
      have himage : image d = image e := congrArg Subtype.val hde
      have hreg :
          ∃! r : D,
            (r : H) * (z : H) * (r : H)⁻¹ = (image d : H) := by
        simpa [H, D, b'] using
          (huppert_blackburn_XI_sharpTriple_kernel_conj_regular
            htwo hsharp a b hab F hFrob z (image d) hz (himage_ne d))
      have hd : (d : H) * (z : H) * (d : H)⁻¹ = (image d : H) := rfl
      have he : (e : H) * (z : H) * (e : H)⁻¹ = (image d : H) := by
        change (image e : H) = (image d : H)
        exact congrArg Subtype.val himage.symm
      exact hreg.unique hd he
    · intro y
      have hreg :
          ∃! d : D,
            (d : H) * (z : H) * (d : H)⁻¹ = (y.1 : H) := by
        simpa [H, D, b'] using
          (huppert_blackburn_XI_sharpTriple_kernel_conj_regular
            htwo hsharp a b hab F hFrob z y.1 hz y.2)
      obtain ⟨d, hd, _⟩ := hreg
      refine ⟨d, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact hd
  let e : D ≃ {x : F // x ≠ 1} := Equiv.ofBijective phi hphi
  refine ⟨z, hz, e, ?_⟩
  intro d
  rfl


set_option backward.isDefEq.respectTransparency false in
/-- In the sharply triply transitive branch, the Frobenius kernel of a point
stabilizer is elementary abelian and has prime-power order equal to the degree
minus one. -/
public theorem huppert_blackburn_XI_sharpTriple_kernel_elementaryAbelian
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    [Fintype Omega]
    (n : ℕ) (hdegree : Fintype.card Omega = n + 1)
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (hsharp :
      ∀ a b c a' b' c' : Omega,
        a ≠ b → a ≠ c → b ≠ c →
        a' ≠ b' → a' ≠ c' → b' ≠ c' →
        ∃! g : G,
          g • a = a' ∧ g • b = b' ∧ g • c = c')
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob :
      IsFrobeniusGroupWithKernelComplement F
        (MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a))) :
    ∃ p f : ℕ, Nat.Prime p ∧ 0 < f ∧ n = p ^ f ∧
      IsElementaryAbelian p F := by
  classical
  let H := MulAction.stabilizer G a
  let X := SubMulAction.ofStabilizer G a
  let b' : X := ⟨b, hab.symm⟩
  let D := MulAction.stabilizer H b'
  change IsFrobeniusGroupWithKernelComplement F D at hFrob
  have hFcard : Nat.card F = n :=
    huppert_blackburn_XI_pointStabilizer_frobeniusKernel_card
      n hdegree htwo a b hab F hFrob
  have hconj_transitive :
      ∀ x y : F, x ≠ 1 → y ≠ 1 →
        ∃ d : D, (d : H) * (x : H) * (d : H)⁻¹ = (y : H) := by
    intro x y hx hy
    simpa [H, D, b'] using
      (huppert_blackburn_XI_sharpTriple_kernel_conj_regular
        htwo hsharp a b hab F hFrob x y hx hy).exists
  have hFnontrivial : Nontrivial F :=
    (Subgroup.nontrivial_iff_ne_bot F).2 hFrob.kernel_ne_bot
  letI : Nontrivial F := hFnontrivial
  have hFcard_ne_one : Nat.card F ≠ 1 := by
    exact ne_of_gt (Finite.one_lt_card_iff_nontrivial.mpr hFnontrivial)
  obtain ⟨p, hp, hp_dvd⟩ := Nat.exists_prime_and_dvd hFcard_ne_one
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  obtain ⟨z, hzorder⟩ := exists_prime_orderOf_dvd_card' p hp_dvd
  have hzne : z ≠ 1 := by
    intro hz
    have : p = 1 := by simpa [hz] using hzorder.symm
    exact hp.ne_one this
  have hprime_order (x : F) (hx : x ≠ 1) : orderOf x = p := by
    obtain ⟨d, hd⟩ := hconj_transitive x z hx hzne
    have hsemi : SemiconjBy (d : H) (x : H) (z : H) := by
      change (d : H) * (x : H) = (z : H) * (d : H)
      calc
        (d : H) * (x : H) =
            ((d : H) * (x : H) * (d : H)⁻¹) * (d : H) := by group
        _ = (z : H) * (d : H) := by rw [hd]
    calc
      orderOf x = orderOf (x : H) :=
        (orderOf_injective F.subtype F.subtype_injective x).symm
      _ = orderOf (z : H) := SemiconjBy.orderOf_eq (d : H) hsemi
      _ = orderOf z := orderOf_injective F.subtype F.subtype_injective z
      _ = p := hzorder
  have hFp : IsPGroup p F := (IsPGroup.iff_orderOf).2 (by
    intro x
    by_cases hx : x = 1
    · exact ⟨0, by simp [hx]⟩
    · exact ⟨1, by simp [hprime_order x hx]⟩)
  have hFcomm : IsMulCommutative F := by
    letI : Nontrivial (Subgroup.center F) := hFp.center_nontrivial
    obtain ⟨zc, hzc⟩ := exists_ne (1 : Subgroup.center F)
    let zF : F := zc
    have hzF_ne : zF ≠ 1 := by
      intro hzF
      apply hzc
      exact Subtype.ext hzF
    refine IsMulCommutative.mk <| Std.Commutative.mk <| fun x y => ?_
    by_cases hx : x = 1
    · simp [hx]
    obtain ⟨d, hd⟩ := hconj_transitive x zF hx hzF_ne
    let ydy : F :=
      ⟨(d : H) * (y : H) * (d : H)⁻¹,
        hFrob.normal.conj_mem (y : H) y.property (d : H)⟩
    have hz_comm : zF * ydy = ydy * zF :=
      ((Subgroup.mem_center_iff.mp zc.property) ydy).symm
    have hz_comm_H :
        (zF : H) * ((d : H) * (y : H) * (d : H)⁻¹) =
          ((d : H) * (y : H) * (d : H)⁻¹) * (zF : H) := by
      simpa [ydy, zF] using congrArg Subtype.val hz_comm
    apply Subtype.ext
    change (x : H) * (y : H) = (y : H) * (x : H)
    calc
      (x : H) * (y : H) =
          (d : H)⁻¹ * (zF : H) * (d : H) * (y : H) := by
            rw [← hd]
            group
      _ = (d : H)⁻¹ *
          ((zF : H) * ((d : H) * (y : H) * (d : H)⁻¹)) * (d : H) := by
            group
      _ = (d : H)⁻¹ *
          (((d : H) * (y : H) * (d : H)⁻¹) * (zF : H)) * (d : H) := by
            rw [hz_comm_H]
      _ = (y : H) * ((d : H)⁻¹ * (zF : H) * (d : H)) := by
            group
      _ = (y : H) * (x : H) := by
            rw [← hd]
            group
  have hFelem : IsElementaryAbelian p F := by
    refine
      { toIsMulCommutative := hFcomm
        exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_ }
    intro x
    by_cases hx : x = 1
    · simp [hx]
    apply orderOf_dvd_iff_pow_eq_one.mp
    rw [hprime_order x hx]
  obtain ⟨f, hFpow⟩ := hFp.exists_card_eq
  have hfpos : 0 < f := by
    by_contra hf
    have hfzero : f = 0 := Nat.eq_zero_of_not_pos hf
    have : Nat.card F = 1 := by simpa [hfzero] using hFpow
    exact hFcard_ne_one this
  exact ⟨p, f, hp, hfpos, hFcard.symm.trans hFpow, hFelem⟩

/-- In the sharply triply transitive branch, the Frobenius kernel of a point
stabilizer has prime-power order, equal to the degree minus one. This is the
prime-power consequence for which XI.11.16 cites XI.2.1. -/
public theorem huppert_blackburn_XI_sharpTriple_degree_primePower
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    [Fintype Omega]
    (n : ℕ) (hdegree : Fintype.card Omega = n + 1)
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (hsharp :
      ∀ a b c a' b' c' : Omega,
        a ≠ b → a ≠ c → b ≠ c →
        a' ≠ b' → a' ≠ c' → b' ≠ c' →
        ∃! g : G,
          g • a = a' ∧ g • b = b' ∧ g • c = c')
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob :
      IsFrobeniusGroupWithKernelComplement F
        (MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a))) :
    ∃ p f : ℕ, Nat.Prime p ∧ 0 < f ∧ n = p ^ f := by
  rcases huppert_blackburn_XI_sharpTriple_kernel_elementaryAbelian
      n hdegree htwo hsharp a b hab F hFrob with
    ⟨p, f, hp, hf, hn, _hFelem⟩
  exact ⟨p, f, hp, hf, hn⟩

end External
end CFSG.BenderSuzuki
