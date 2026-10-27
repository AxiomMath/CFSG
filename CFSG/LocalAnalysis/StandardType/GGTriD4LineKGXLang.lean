module

public import CFSG.LocalAnalysis.StandardType.GGTriD4LineKGXRoot
public import CFSG.LocalAnalysis.StandardType.GGTriD4LineKGXTorus
public import CFSG.LocalAnalysis.StandardType.GGTriD4LineKGXSL3

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KGD

open scoped Pointwise

private lemma units_map_eq_pow {L : Type} [Field L] (Fr : L →+* L) (q : ℕ)
    (hFr : ∀ c, Fr c = c ^ q) (v : Lˣ) :
    Units.map Fr.toMonoidHom v = v ^ q := by
  ext
  exact hFr v

private lemma exists_unit_pow_eq {L : Type} [Field L] [IsAlgClosed L] {n : ℕ} (hn : 0 < n)
    (u : Lˣ) : ∃ v : Lˣ, v ^ n = u := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (u : L) hn
  have hz0 : z ≠ 0 := by
    intro h
    subst h
    rw [zero_pow (show n ≠ 0 from hn.ne')] at hz
    exact u.ne_zero hz.symm
  refine ⟨Units.mk0 z hz0, Units.ext ?_⟩
  rw [Units.val_pow_eq_pow_val, Units.val_mk0, hz]

private lemma d4Lang_tuple {L : Type} [Field L] (Fr : L →+* L) (q : ℕ)
    (hFr : ∀ c, Fr c = c ^ q) (s' t' : Lˣ) (b v : Fin TwistTag.D4.tag.rank → Lˣ)
    (hv : v = ![s', s', t', s'])
    (hb1 : b 1 = b 0) (hb3 : b 3 = b 0)
    (hs' : s' ^ (q - 1) = b 0) (ht' : t' ^ (q - 1) = b 2) (hq1 : 1 ≤ q) :
    (fun i => Units.map Fr.toMonoidHom (v (TwistTag.D4.perm.symm i))) = v * b := by
  rw [hv]
  funext i
  obtain ⟨n, hn⟩ := i
  have hn' : n < 4 := hn
  interval_cases n
  · show Units.map Fr.toMonoidHom s' = s' * b 0
    rw [units_map_eq_pow Fr q hFr, ← hs', ← pow_succ', Nat.sub_add_cancel hq1]
  · show Units.map Fr.toMonoidHom s' = s' * b 1
    rw [hb1, units_map_eq_pow Fr q hFr, ← hs', ← pow_succ', Nat.sub_add_cancel hq1]
  · show Units.map Fr.toMonoidHom t' = t' * b 2
    rw [units_map_eq_pow Fr q hFr, ← ht', ← pow_succ', Nat.sub_add_cancel hq1]
  · show Units.map Fr.toMonoidHom s' = s' * b 3
    rw [hb3, units_map_eq_pow Fr q hFr, ← hs', ← pow_succ', Nat.sub_add_cancel hq1]

theorem triD4Line_fixed_mul_Qv
    (L : Type) [Field L] [CharP L 2] [IsAlgClosed L] (q : ℕ) (hq : 2 ≤ q) (Fr : L →+* L)
    (hFr : ∀ c, Fr c = c ^ q) (A : Lˣ) (hA3 : A ^ 3 = 1) (hA1 : A ≠ 1) (g : ModGL Tag.D4 L)
    (hg : g ∈ toralCentralizer Tag.D4 L ![A, A, 1, A])
    (hgF : twistHom TwistTag.D4 L Fr g = g) :
    ∃ h ∈ torusGroup Tag.D4 L, twistHom TwistTag.D4 L Fr h = h ∧
      ∃ m ∈ d4A2Qv L triD4LineV, twistHom TwistTag.D4 L Fr m = m ∧ g = h * m := by
  have hcent := (triD4Line_toralCentralizer_z0 L A hA3 hA1).2.2.1
  have hg' : g ∈ (torusGroup Tag.D4 L : Set (ModGL Tag.D4 L)) *
      (d4A2Qv L triD4LineV : Set (ModGL Tag.D4 L)) := by
    rw [← hcent]
    exact hg
  rw [Set.mem_mul] at hg'
  obtain ⟨h₀, hh₀H, m₀, hm₀Q, hg_eq⟩ := hg'
  let Φ : ModGL Tag.D4 L →* ModGL Tag.D4 L := twistHom TwistTag.D4 L Fr
  have hgF' : Φ g = g := hgF
  set δ : ModGL Tag.D4 L := h₀⁻¹ * Φ h₀ with hδdef
  have hmul : h₀ * m₀ = Φ h₀ * Φ m₀ := by
    rw [← map_mul, hg_eq, hgF']
  have hδm : δ * Φ m₀ = m₀ := by
    rw [hδdef, mul_assoc, ← hmul, ← mul_assoc, inv_mul_cancel, one_mul]
  obtain ⟨b₀, hb₀⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh₀H
  have hΦh₀H : Φ h₀ ∈ torusGroup Tag.D4 L := by
    rw [hb₀]
    rw [show Φ (rootDiagUnit Tag.D4 b₀) =
        rootDiagUnit Tag.D4 (fun i => Units.map Fr.toMonoidHom (b₀ (TwistTag.D4.perm.symm i)))
      from twistHom_rootDiagUnit_eq (t := TwistTag.D4) (σ := Fr) b₀]
    exact rootDiagUnit_mem_torusGroup _
  have hδH : δ ∈ torusGroup Tag.D4 L := by
    rw [hδdef]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hh₀H) hΦh₀H
  obtain ⟨hm₀entry, -⟩ := triD4Line_entrywise_d4A2Qv L Fr m₀ hm₀Q
  have hΦm₀Q : Φ m₀ ∈ d4A2Qv L triD4LineV := by
    rw [show Φ m₀ = Units.map (entrywiseHom Fr) m₀ from
      triD4Line_twistHom_eq_entrywise L Fr m₀ hm₀Q]
    exact hm₀entry
  have hδQ : δ ∈ d4A2Qv L triD4LineV := by
    have hδeq : δ = m₀ * (Φ m₀)⁻¹ := by
      nth_rewrite 1 [← hδm]
      rw [mul_assoc, mul_inv_cancel, mul_one]
    rw [hδeq]
    exact Subgroup.mul_mem _ hm₀Q (Subgroup.inv_mem _ hΦm₀Q)
  obtain ⟨b, hδb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hδH
  have hbQ : rootDiagUnit Tag.D4 b ∈ d4A2Qv L triD4LineV := by
    rw [← hδb]
    exact hδQ
  obtain ⟨hb1, hb3⟩ := (triD4Line_rootDiagUnit_mem_Qv_iff L b).1 hbQ
  have hq1 : 1 ≤ q := by omega
  obtain ⟨s', hs'⟩ := exists_unit_pow_eq (L := L) (n := q - 1) (by omega) (b 0)
  obtain ⟨t', ht'⟩ := exists_unit_pow_eq (L := L) (n := q - 1) (by omega) (b 2)
  let b' : Fin TwistTag.D4.tag.rank → Lˣ := b
  have hb1' : b' 1 = b' 0 := hb1
  have hb3' : b' 3 = b' 0 := hb3
  have hs'' : s' ^ (q - 1) = b' 0 := hs'
  have ht'' : t' ^ (q - 1) = b' 2 := ht'
  have hδb' : δ = rootDiagUnit TwistTag.D4.tag b' := hδb
  set v : Fin TwistTag.D4.tag.rank → Lˣ := ![s', s', t', s'] with hv
  set x : ModGL Tag.D4 L := rootDiagUnit TwistTag.D4.tag v with hx
  have hxH : x ∈ torusGroup Tag.D4 L := by
    rw [hx]
    exact rootDiagUnit_mem_torusGroup v
  have hxQ : x ∈ d4A2Qv L triD4LineV := by
    rw [hx]
    refine (triD4Line_rootDiagUnit_mem_Qv_iff L v).2 ⟨?_, ?_⟩
    · rw [hv]
      rfl
    · rw [hv]
      rfl
  have htuple := d4Lang_tuple Fr q hFr s' t' b' v hv hb1' hb3' hs'' ht'' hq1
  have hPhiX : Φ x = x * δ := by
    rw [hx, hδb']
    rw [show Φ (rootDiagUnit TwistTag.D4.tag v) =
        rootDiagUnit TwistTag.D4.tag
          (fun i => Units.map Fr.toMonoidHom (v (TwistTag.D4.perm.symm i)))
      from twistHom_rootDiagUnit_eq (t := TwistTag.D4) (σ := Fr) v]
    rw [htuple, rootDiagUnit_mul]
    rfl
  have hΦh₀ : Φ h₀ = h₀ * δ := by
    rw [hδdef, ← mul_assoc, mul_inv_cancel, one_mul]
  refine ⟨h₀ * x⁻¹, Subgroup.mul_mem _ hh₀H (Subgroup.inv_mem _ hxH), ?_,
    x * m₀, Subgroup.mul_mem _ hxQ hm₀Q, ?_, ?_⟩
  · change Φ (h₀ * x⁻¹) = h₀ * x⁻¹
    rw [map_mul, map_inv, hPhiX, hΦh₀]
    group
  · change Φ (x * m₀) = x * m₀
    rw [map_mul, hPhiX, mul_assoc, hδm]
  · rw [← hg_eq]
    group

end CFSG.StandardType
