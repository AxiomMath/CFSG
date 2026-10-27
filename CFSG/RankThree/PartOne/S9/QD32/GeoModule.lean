module

public import CFSG.RankThree.PartOne.S9.QD32.Basic
public import CFSG.RankThree.PartOne.S9.OddCore.TorsionModule
public import CFSG.RankThree.PartOne.S9.OddCore.TorsionBridge
public import CFSG.RankThree.GroupTheory.SteinbergBMMinimalExtraspecialModule
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.PartOne.QD32Facts

open CFSG CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne.FixedRank36
  CFSG.RankThree.PartOne.Torsion37 Subgroup
open scoped commutatorElement IsMulCommutative

variable {G : Type*} [Group G]

theorem mem_inSubgroup_frattini_of_mk_eq_one {D : Subgroup G} {x : ↥D}
    (h : (x : ↥D ⧸ frattini ↥D) = 1) : (x : G) ∈ inSubgroup frattini D :=
  ⟨x, (QuotientGroup.eq_one_iff x).mp h, rfl⟩

theorem mk_eq_one_of_mem_inSubgroup_frattini {D : Subgroup G} {x : ↥D}
    (h : (x : G) ∈ inSubgroup frattini D) : (x : ↥D ⧸ frattini ↥D) = 1 := by
  obtain ⟨y, hy, hyx⟩ := h
  have : y = x := Subtype.ext hyx
  rw [← this]
  exact (QuotientGroup.eq_one_iff y).mpr hy

theorem exists_split_of_involution {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (h2 : (2 : K) ≠ 0) (T : V →ₗ[K] V) (hT : ∀ v, T (T v) = v) (v : V) :
    ∃ a b : V, v = a + b ∧ T a = a ∧ T b = -b := by
  refine ⟨(2 : K)⁻¹ • (v + T v), (2 : K)⁻¹ • (v - T v), ?_, ?_, ?_⟩
  · rw [← smul_add, add_add_sub_cancel, ← two_smul K v, smul_smul, inv_mul_cancel₀ h2, one_smul]
  · rw [map_smul, map_add, hT, add_comm]
  · rw [map_smul, map_sub, hT, ← smul_neg, neg_sub]

theorem frattini_module_geometry {G : Type} [Group G] [Finite G] {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) {D S B : Subgroup G} (hD : IsPGroup q D)
    (hrel : (inSubgroup frattini D).relIndex D = q ^ 4)
    (hSD : S ≤ normalizer (D : Set G)) (hBD : B ≤ normalizer (D : Set G))
    (hBS : B ≤ centralizer (S : Set G)) (hS : Nonempty (S ≃* QD32))
    (hSC : S ⊓ centralizer (D : Set G) = ⊥)
    (hSΦ : ∀ s ∈ S, ∀ ζ ∈ inSubgroup frattini D, s * ζ = ζ * s) :
    (∀ z ∈ S, z ≠ 1 → z ∈ inSubgroup Subgroup.center S →
      ∀ d ∈ D, z * d * z⁻¹ * d ∈ inSubgroup frattini D) ∧
    (∀ r ∈ S, orderOf r = 2 → r ∉ inSubgroup Subgroup.center S →
      (∀ d ∈ D, ∃ f ∈ D, r * f * r⁻¹ = f ∧
        ∃ m ∈ D, d = f * m ∧ r * m * r⁻¹ * m ∈ inSubgroup frattini D) ∧
      Nat.card ↥(D ⊓ centralizer ({r} : Set G)) = Nat.card (inSubgroup frattini D) * q ^ 2) ∧
    (∀ b ∈ B, ∃ l : ℕ, ∀ d ∈ D, b * d * b⁻¹ * (d ^ l)⁻¹ ∈ inSubgroup frattini D) := by
  classical
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨φ⟩ := hS
  obtain ⟨hcard32, hext, -, -⟩ :=
    SteinbergBY.quaternion_dihedral_extraspecial_involution_generation
  have hSext : IsExtraspecialPGroup 2 ↥S := isExtraspecialPGroup_of_mulEquiv φ.symm hext
  have hS32 : Nat.card ↥S = 2 ^ (1 + 2 * 2) := by
    rw [Nat.card_congr φ.toEquiv, hcard32]
    norm_num
  obtain ⟨z₀, hz₀ord, hz₀c, -⟩ := exists_data_of_equiv_QD32 φ
  have hel : IsElementaryAbelian q (↥D ⧸ frattini ↥D) :=
    (CFSG.GroupTheory.frattini_elementary_quotient hD).2.2.2.1
  have hfd : FiniteDimensional (ZMod q) (Additive (↥D ⧸ frattini ↥D)) := Module.Finite.of_finite
  set ρY : ↥(normalizer (D : Set G)) →* MulAut ↥D := D.normalizerMonoidHom with hρY
  set ρS : ↥S →* MulAut ↥D := ρY.comp (Subgroup.inclusion hSD) with hρS
  have hR2 : IsPGroup 2 ↥S := hSext.1
  have hdim : Module.finrank (ZMod q) (Additive (↥D ⧸ frattini ↥D)) = 4 := by
    have h1 : Nat.card (↥D ⧸ frattini ↥D) = q ^ 4 := by
      rw [← relIndex_inSubgroup_frattini_eq_card, hrel]
    have h2 : Nat.card (Additive (↥D ⧸ frattini ↥D)) = q ^ 4 := by
      rw [← h1]
      exact Nat.card_congr Additive.toMul
    rw [Module.natCard_eq_pow_finrank (K := ZMod q), Nat.card_zmod] at h2
    exact Nat.pow_right_injective hq.two_le h2
  have hVnt : Nontrivial (Additive (↥D ⧸ frattini ↥D)) :=
    Module.nontrivial_of_finrank_pos (R := ZMod q) (by omega)
  have hinj : Function.Injective (frattiniRep q ρS) := by
    rw [injective_iff_map_eq_one]
    intro r hr
    have h1 : ρS r = 1 :=
      frattiniRep_eq_one hD hq2 ρS r (isPGroup_zpowers_map hR2 ρS r) hr
    have hmem : (r : G) ∈ S ⊓ centralizer (D : Set G) := by
      refine ⟨r.2, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
      have h := congrArg (fun f : MulAut ↥D => ((f ⟨g, hg⟩ : ↥D) : G)) h1
      simp only [hρS, hρY, MonoidHom.comp_apply, MulAut.one_apply] at h
      change (r : G) * g * (r : G)⁻¹ = g at h
      calc g * (r : G) = ((r : G) * g * (r : G)⁻¹) * r := by rw [h]
        _ = r * g := by group
    rw [hSC, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  obtain ⟨hρz, -, hcent, -⟩ :=
    SteinbergBM.minimal_extraspecial_module_scalar_centralizer.{0, 0, 0, 0}
    hSext hS32 hz₀c (K := ZMod q) (by rw [ZMod.ringChar_zmod_n]; exact hq2) hdim
    (frattiniRep q ρS) hinj
  refine ⟨?_, ?_, ?_⟩
  ·
    intro z hzS hz1 hzc d hd
    have hz' : (⟨z, hzS⟩ : ↥S) = z₀ := by
      have hmem : (⟨z, hzS⟩ : ↥S) ∈ Subgroup.center ↥S := by
        obtain ⟨c, hc, hcz⟩ := hzc
        have : c = ⟨z, hzS⟩ := Subtype.ext hcz
        rwa [← this]
      rw [hz₀c, SteinbergBY.mem_zpowers_of_orderOf_eq_two hz₀ord] at hmem
      rcases hmem with h | h
      · exact absurd (congrArg Subtype.val h) hz1
      · exact h
    have hρz' : frattiniRep q ρS ⟨z, hzS⟩ = -1 := by rw [hz']; exact hρz
    have h := congrArg (fun f : Module.End (ZMod q) (Additive (↥D ⧸ frattini ↥D)) =>
        f (Additive.ofMul ((⟨d, hd⟩ : ↥D) : ↥D ⧸ frattini ↥D))) hρz'
    simp only [frattiniRep_apply, LinearMap.neg_apply, Module.End.one_apply] at h
    have h' : (((ρS ⟨z, hzS⟩ ⟨d, hd⟩ : ↥D)) : ↥D ⧸ frattini ↥D) =
        ((⟨d, hd⟩ : ↥D) : ↥D ⧸ frattini ↥D)⁻¹ := by
      have := congrArg Additive.toMul h
      simpa using this
    have h1 : (((ρS ⟨z, hzS⟩ ⟨d, hd⟩ * ⟨d, hd⟩ : ↥D)) : ↥D ⧸ frattini ↥D) = 1 := by
      rw [QuotientGroup.mk_mul, h', inv_mul_cancel]
    exact mem_inSubgroup_frattini_of_mk_eq_one h1
  ·
    intro r hrS hr2 hrc
    have hrS' : (⟨r, hrS⟩ : ↥S) ∉ Subgroup.center ↥S := fun h => hrc ⟨⟨r, hrS⟩, h, rfl⟩
    have hord : orderOf (⟨r, hrS⟩ : ↥S) = 2 := by
      rw [← hr2]
      exact Subgroup.orderOf_mk r hrS
    set r' : ↥S := ⟨r, hrS⟩ with hr'
    set T := frattiniRep q ρS r' with hT
    have hrr : r' * r' = 1 := by
      rw [← pow_two, ← hord]
      exact pow_orderOf_eq_one r'
    have hTT : ∀ v, T (T v) = v := by
      intro v
      rw [hT, ← Module.End.mul_apply, ← map_mul, hrr, map_one, Module.End.one_apply]
    have hl : IsPGroup 2 (Subgroup.zpowers (ρS r')) := isPGroup_zpowers_map hR2 ρS r'
    have hbound : 2 * Module.finrank (ZMod q) (Module.End.eigenspace T 1) =
        Module.finrank (ZMod q) (Additive (↥D ⧸ frattini ↥D)) :=
      ((extraspecial_two_minus_module_bound hSext hS32 hz₀c
        (two_ne_zero_zmod hq hq2) (frattiniRep q ρS) hρz).2 r' hrS' hord).1
    have hfin : Module.finrank (ZMod q) (Module.End.eigenspace T 1) = 2 := by
      rw [hdim] at hbound
      omega
    have hcoe : ∀ x : ↥D, ((ρS r' x : ↥D) : G) = r * (x : G) * r⁻¹ := fun x => rfl
    refine ⟨?_, ?_⟩
    ·
      intro d hd
      obtain ⟨a, b, hab, hTa, hTb⟩ := exists_split_of_involution (two_ne_zero_zmod hq hq2) T hTT
        (Additive.ofMul ((⟨d, hd⟩ : ↥D) : ↥D ⧸ frattini ↥D))
      obtain ⟨x, hxfix, hxa⟩ := exists_fixed_lift hD hq2 ρS r' hl a
        (by rw [Module.End.mem_eigenspace_iff, one_smul]; exact hTa)
      have hxb : Additive.ofMul (((x⁻¹ * ⟨d, hd⟩ : ↥D)) : ↥D ⧸ frattini ↥D) = b := by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, ofMul_mul, ofMul_inv, hxa]
        have : a + b = Additive.ofMul ((⟨d, hd⟩ : ↥D) : ↥D ⧸ frattini ↥D) := hab.symm
        rw [← this]
        abel
      refine ⟨(x : G), x.2, ?_, ((x⁻¹ * ⟨d, hd⟩ : ↥D) : G), (x⁻¹ * ⟨d, hd⟩).2, ?_, ?_⟩
      · have := congrArg (fun f : ↥D => (f : G)) hxfix
        simpa [hcoe] using this
      · simp
      · have h1 : T (Additive.ofMul (((x⁻¹ * ⟨d, hd⟩ : ↥D)) : ↥D ⧸ frattini ↥D)) =
            -Additive.ofMul (((x⁻¹ * ⟨d, hd⟩ : ↥D)) : ↥D ⧸ frattini ↥D) := by
          rw [hxb]
          exact hTb
        rw [hT, frattiniRep_apply] at h1
        have h2 := congrArg Additive.toMul h1
        simp only [toMul_ofMul, toMul_neg] at h2
        have h3 : (((ρS r' (x⁻¹ * ⟨d, hd⟩) * (x⁻¹ * ⟨d, hd⟩) : ↥D)) : ↥D ⧸ frattini ↥D) = 1 := by
          rw [QuotientGroup.mk_mul, h2, inv_mul_cancel]
        exact mem_inSubgroup_frattini_of_mk_eq_one h3
    ·
      set F : Subgroup G := D ⊓ centralizer ({r} : Set G) with hF
      have hΦD : inSubgroup frattini D ≤ D := Subgroup.map_subtype_le _
      have hΦF : inSubgroup frattini D ≤ F := fun ζ hζ =>
        ⟨hΦD hζ, Subgroup.mem_centralizer_singleton_iff.mpr (hSΦ r hrS ζ hζ).symm⟩
      let g : ↥F →* ↥D ⧸ frattini ↥D :=
        (QuotientGroup.mk' (frattini ↥D)).comp (Subgroup.inclusion (inf_le_left : F ≤ D))
      have hker : g.ker = (inSubgroup frattini D).subgroupOf F := by
        ext f
        rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
        constructor
        · intro h
          exact mem_inSubgroup_frattini_of_mk_eq_one h
        · intro h
          exact mk_eq_one_of_mem_inSubgroup_frattini h
      have hkercard : Nat.card g.ker = Nat.card (inSubgroup frattini D) := by
        rw [hker]
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hΦF).toEquiv
      have hrangecard : Nat.card g.range = q ^ 2 := by
        have e1 : Nat.card g.range = Nat.card (Module.End.eigenspace T 1) := by
          refine Nat.card_congr
            { toFun := fun w => ⟨Additive.ofMul (w : ↥D ⧸ frattini ↥D), ?_⟩
              invFun := fun v => ⟨Additive.toMul (v : Additive (↥D ⧸ frattini ↥D)), ?_⟩
              left_inv := fun w => Subtype.ext rfl
              right_inv := fun v => Subtype.ext rfl }
          · obtain ⟨f, hf⟩ := w.2
            rw [Module.End.mem_eigenspace_iff, one_smul, ← hf]
            change T (Additive.ofMul (((Subgroup.inclusion (inf_le_left : F ≤ D) f : ↥D)) :
              ↥D ⧸ frattini ↥D)) = _
            have hfix : ρS r' (Subgroup.inclusion (inf_le_left : F ≤ D) f) =
                Subgroup.inclusion (inf_le_left : F ≤ D) f := by
              apply Subtype.ext
              rw [hcoe]
              have := Subgroup.mem_centralizer_singleton_iff.mp f.2.2
              change r * (f : G) * r⁻¹ = f
              calc r * (f : G) * r⁻¹ = (f : G) * r * r⁻¹ := by rw [← this]
                _ = f := by group
            rw [hT, frattiniRep_apply, hfix]
            rfl
          · obtain ⟨x, hxfix, hxv⟩ := exists_fixed_lift hD hq2 ρS r' hl v.1 v.2
            have hxF : (x : G) ∈ F := by
              refine ⟨x.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
              have := congrArg (fun f : ↥D => (f : G)) hxfix
              change r * (x : G) * r⁻¹ = x at this
              calc (x : G) * r = (r * (x : G) * r⁻¹) * r := by rw [this]
                _ = r * x := by group
            refine ⟨⟨x, hxF⟩, ?_⟩
            change (QuotientGroup.mk' (frattini ↥D)) (Subgroup.inclusion (inf_le_left : F ≤ D)
              ⟨x, hxF⟩) = _
            rw [← hxv]
            rfl
        rw [e1, Module.natCard_eq_pow_finrank (K := ZMod q), Nat.card_zmod, hfin]
      have hmul := Subgroup.card_ker_mul_card_range g
      rw [hkercard, hrangecard] at hmul
      exact hmul.symm
  ·
    intro b hb
    set bY : ↥(normalizer (D : Set G)) := ⟨b, hBD hb⟩ with hbY
    set u : (Module.End (ZMod q) (Additive (↥D ⧸ frattini ↥D)))ˣ :=
      (frattiniRep q ρY).asGroupHom bY with hu
    have hucent : u ∈ Subgroup.centralizer (Set.range (frattiniRep q ρS).asGroupHom) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨s, rfl⟩
      have hcomm : (⟨s.1, hSD s.2⟩ : ↥(normalizer (D : Set G))) * bY =
          bY * ⟨s.1, hSD s.2⟩ :=
        Subtype.ext (Subgroup.mem_centralizer_iff.mp (hBS hb) s.1 s.2)
      have := congrArg (frattiniRep q ρY).asGroupHom hcomm
      rw [map_mul, map_mul] at this
      exact this
    rw [hcent] at hucent
    obtain ⟨c, hc⟩ := hucent
    have hcv : ∀ v : Additive (↥D ⧸ frattini ↥D),
        frattiniRep q ρY bY v = (c : ZMod q) • v := by
      intro v
      have h1 := congrArg (fun w : (Module.End (ZMod q) (Additive (↥D ⧸ frattini ↥D)))ˣ =>
        (w : Module.End (ZMod q) (Additive (↥D ⧸ frattini ↥D))) v) hc
      simpa [hu, Representation.asGroupHom_apply, Module.algebraMap_end_apply] using h1.symm
    refine ⟨(c : ZMod q).val, fun d hd => ?_⟩
    have h := hcv (Additive.ofMul ((⟨d, hd⟩ : ↥D) : ↥D ⧸ frattini ↥D))
    rw [frattiniRep_apply] at h
    have hc' : (c : ZMod q) • Additive.ofMul ((⟨d, hd⟩ : ↥D) : ↥D ⧸ frattini ↥D) =
        (c : ZMod q).val • Additive.ofMul ((⟨d, hd⟩ : ↥D) : ↥D ⧸ frattini ↥D) := by
      rw [← Nat.cast_smul_eq_nsmul (ZMod q), ZMod.natCast_zmod_val]
    rw [hc'] at h
    have h' := congrArg Additive.toMul h
    rw [toMul_nsmul, toMul_ofMul, toMul_ofMul] at h'
    have h1 : (((ρY bY ⟨d, hd⟩ * ((⟨d, hd⟩ : ↥D) ^ (c : ZMod q).val)⁻¹ : ↥D)) :
        ↥D ⧸ frattini ↥D) = 1 := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_pow, h', mul_inv_cancel]
    exact mem_inSubgroup_frattini_of_mk_eq_one h1

end CFSG.RankThree.PartOne.QD32Facts

