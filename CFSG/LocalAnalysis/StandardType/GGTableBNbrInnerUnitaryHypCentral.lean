module

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerMonomialIrred
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryTorus
public import CFSG.LieType.Steinberg.CentralExt.PSUMultiplier
public import CFSG.ClassicalGroups.Unitary.Simple
public import CFSG.ClassicalGroups.UnitaryFlag.ModelTransport

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

section Cover

theorem exists_cover_of_sections {H R L' : Type} [Group H] [Finite H] [Group R] [Group L']
    [Finite L'] (pr : H →* R) (hpr : Function.Surjective pr)
    (hsec : ∀ (E : Type) [Group E] [Finite E] (π : E →* H), Function.Surjective π →
      π.ker ≤ Subgroup.center E → ∃ σ : H →* E, ∀ g, π (σ g) = g)
    (ψ : L' →* R) (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤) :
    ∃ φ : H →* L', Function.Surjective φ ∧ ∀ g, ψ (φ g) = pr g := by
  let E : Subgroup (L' × H) :=
    MonoidHom.eqLocus (ψ.comp (MonoidHom.fst L' H)) (pr.comp (MonoidHom.snd L' H))
  let π : E →* H := (MonoidHom.snd L' H).comp E.subtype
  have hπ : Function.Surjective π := by
    intro s
    obtain ⟨l, hl⟩ := hψ (pr s)
    exact ⟨⟨(l, s), hl⟩, rfl⟩
  have hcen : π.ker ≤ Subgroup.center E := by
    rintro ⟨⟨l, s⟩, hx⟩ hk
    have hs : s = 1 := hk
    have hx' : ψ l = pr s := hx
    have hl : l ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, hx', hs, map_one]
    rw [Subgroup.mem_center_iff]
    rintro ⟨⟨l', s'⟩, hy⟩
    apply Subtype.ext
    change (l' * l, s' * s) = (l * l', s * s')
    rw [hs, one_mul, mul_one, (Subgroup.mem_center_iff.mp (hker hl)) l']
  obtain ⟨σ, hσ⟩ := hsec E π hπ hcen
  let φ : H →* L' := (MonoidHom.fst L' H).comp (E.subtype.comp σ)
  have hφ : ∀ g, ψ (φ g) = pr g := by
    intro g
    have h1 : ψ ((σ g : L' × H).1) = pr ((σ g : L' × H).2) := (σ g).2
    have h2 : (σ g : L' × H).2 = g := hσ g
    change ψ ((σ g : L' × H).1) = _
    rw [h1, h2]
  refine ⟨φ, ?_, hφ⟩
  have hdecomp : ∀ l : L', ∃ s, l * (φ s)⁻¹ ∈ Subgroup.center L' := by
    intro l
    obtain ⟨s, hs⟩ := hpr (ψ l)
    refine ⟨s, hker ?_⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hφ, hs, mul_inv_cancel]
  have htop : (⊤ : Subgroup L') ≤ φ.range := by
    rw [← hperf, _root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    obtain ⟨s, hs⟩ := hdecomp a
    obtain ⟨t, ht⟩ := hdecomp b
    refine ⟨⁅s, t⁆, ?_⟩
    rw [map_commutatorElement]
    have ha : a = (a * (φ s)⁻¹) * φ s := by group
    have hb : b = (b * (φ t)⁻¹) * φ t := by group
    rw [ha, hb, CFSG.LieType.Steinberg.commutatorElement_mul_mul_of_mem_center hs ht]
  intro l
  exact htop (Subgroup.mem_top l)

end Cover

section Centre

variable {n d : ℕ} {F : Type} [Field F] [Finite F]

theorem center_statedProj_statedSU_eq_bot (hF : Nat.card F = (2 ^ n) ^ 2) (hd : 4 ≤ d) :
    Subgroup.center (StatedProj (StatedSU d (2 ^ n) F)) = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 := CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 2) (f := n) hF
  haveI hsimple : IsSimpleGroup (StatedProj (StatedSU d (2 ^ n) F)) :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F 2 n hF d (by omega)
      (fun h => by
        have h1 := congrArg Prod.fst h
        simp only at h1
        omega)
  haveI : Group.IsPerfect (StatedSU d (2 ^ n) F) :=
    CFSG.LieType.Steinberg.CentralExt.SUClosed.isPerfect_statedSU hF hd
  have hperf : Group.IsPerfect (StatedProj (StatedSU d (2 ^ n) F)) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective
      ((StatedScalars (Fin d) F).subgroupOf (StatedSU d (2 ^ n) F)))
  rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center _) with h | h
  · exact h
  · exfalso
    have hcomm : ∀ a b : StatedProj (StatedSU d (2 ^ n) F), a * b = b * a := fun a b =>
      Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a
    have hbot : commutator (StatedProj (StatedSU d (2 ^ n) F)) ≤ ⊥ := by
      rw [_root_.commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact hcomm a b
    obtain ⟨x, hx⟩ := exists_ne (1 : StatedProj (StatedSU d (2 ^ n) F))
    have hx' : x ∈ commutator (StatedProj (StatedSU d (2 ^ n) F)) := by
      rw [hperf.commutator_eq_top]
      exact Subgroup.mem_top x
    exact hx (Subgroup.mem_bot.mp (hbot hx'))

theorem scalars_le_center_statedSU :
    (StatedScalars (Fin d) F).subgroupOf (StatedSU d (2 ^ n) F) ≤
      Subgroup.center (StatedSU d (2 ^ n) F) := fun z hz => by
  have hz' : (z : GL (Fin d) F) ∈ Subgroup.center (GL (Fin d) F) := by
    have h1 := Subgroup.mem_subgroupOf.1 hz
    rwa [StatedScalars, ← Matrix.GeneralLinearGroup.center_eq_range_scalar] at h1
  exact Subgroup.mem_center_iff.2 fun h => Subtype.ext (Subgroup.mem_center_iff.1 hz' h)

theorem center_statedSU_le_scalars (hF : Nat.card F = (2 ^ n) ^ 2) (hd : 4 ≤ d) :
    Subgroup.center (StatedSU d (2 ^ n) F) ≤
      (StatedScalars (Fin d) F).subgroupOf (StatedSU d (2 ^ n) F) := by
  intro z hz
  have hzc : (QuotientGroup.mk z : StatedProj (StatedSU d (2 ^ n) F)) ∈
      Subgroup.center (StatedProj (StatedSU d (2 ^ n) F)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective g
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.mp hz l]
  rw [center_statedProj_statedSU_eq_bot hF hd, Subgroup.mem_bot] at hzc
  exact (QuotientGroup.eq_one_iff z).mp hzc

theorem card_scalars_statedSU_dvd (hF : Nat.card F = (2 ^ n) ^ 2) (hd : 1 ≤ d) :
    Nat.card ((StatedScalars (Fin d) F).subgroupOf (StatedSU d (2 ^ n) F)) ∣ 2 ^ n + 1 := by
  rw [(CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hF hd).2.2]
  exact Nat.gcd_dvd_right _ _

theorem card_center_statedSU_dvd (hF : Nat.card F = (2 ^ n) ^ 2) (hd : 4 ≤ d) :
    Nat.card (Subgroup.center (StatedSU d (2 ^ n) F)) ∣ 2 ^ n + 1 :=
  (Subgroup.card_dvd_of_le (center_statedSU_le_scalars hF hd)).trans
    (card_scalars_statedSU_dvd hF (by omega))

end Centre

section CenterPrime

variable {n d : ℕ} {F : Type} [Field F] [Finite F]

theorem ggCenterPrime_psu_even
    (hF : Nat.card F = (2 ^ n) ^ 2) {p : ℕ}
    (hd : Even d) (hd4 : 4 ≤ d) (hq : 4 ≤ 2 ^ n) (hpq : ¬ p ∣ 2 ^ n + 1) :
    GGCenterPrime p (StatedProj (StatedSU d (2 ^ n) F)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 := CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 2) (f := n) hF
  intro L' _ _ ψ hψ hker hperf hpZ
  obtain ⟨φ, hφs, hφ⟩ := exists_cover_of_sections
    (QuotientGroup.mk' ((StatedScalars (Fin d) F).subgroupOf (StatedSU d (2 ^ n) F)))
    (QuotientGroup.mk'_surjective _)
    (fun E _ _ π hπ hcen =>
      CFSG.LieType.Steinberg.CentralExt.SUClosed.statedSU_exists_section_of_central hF hd hd4 hq
        hπ hcen)
    ψ hψ hker hperf
  have hZker : Subgroup.center L' ≤ ψ.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    have hzc : ψ z ∈ Subgroup.center (StatedProj (StatedSU d (2 ^ n) F)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨l, rfl⟩ := hψ g
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz l]
    rw [center_statedProj_statedSU_eq_bot hF hd4, Subgroup.mem_bot] at hzc
    exact hzc
  have hkerMap : ψ.ker ≤
      ((StatedScalars (Fin d) F).subgroupOf (StatedSU d (2 ^ n) F)).map φ := by
    intro l hl
    obtain ⟨g, rfl⟩ := hφs l
    rw [MonoidHom.mem_ker, hφ g] at hl
    exact Subgroup.mem_map.mpr ⟨g, (QuotientGroup.eq_one_iff g).mp hl, rfl⟩
  have hdvd : Nat.card (Subgroup.center L') ∣ 2 ^ n + 1 :=
    ((Subgroup.card_dvd_of_le (hZker.trans hkerMap)).trans
      (Subgroup.card_map_dvd
        (H := (StatedScalars (Fin d) F).subgroupOf (StatedSU d (2 ^ n) F)) φ)).trans
      (card_scalars_statedSU_dvd hF (by omega))
  exact hpq (dvd_trans hpZ hdvd)

end CenterPrime

section Descent

variable {n r p : ℕ} {F : Type} [Field F] [Finite F]

theorem ggSCWeylIrred_statedProj_of_hypSU (h : UnitaryFieldData 2 n F) (hr : 2 ≤ r)
    (hp : p.Prime) (hpq : ¬ p ∣ 2 ^ n + 1) (hirr : GGSCWeylIrred p 0 (hypSU h r 0)) :
    GGSCWeylIrred p 0 (StatedProj (StatedSU (2 * r) (2 ^ n) F)) := by
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := r) (ε := 0) h
  have hSU : GGSCWeylIrred p 0 (StatedSU (2 * r) (2 ^ n) F) :=
    ggSCWeylIrred_of_mulEquiv (hypTransport h hR).symm hirr
  refine ggSCWeylIrred_of_centralQuotient hp
    (QuotientGroup.mk' ((StatedScalars (Fin (2 * r)) F).subgroupOf (StatedSU (2 * r) (2 ^ n) F)))
    (QuotientGroup.mk'_surjective _) ?_ ?_ hSU
  · rw [QuotientGroup.ker_mk']
    exact scalars_le_center_statedSU
  · exact fun hdvd => hpq (hdvd.trans (card_center_statedSU_dvd h.card_eq_sq (by omega)))

end Descent

end CFSG.StandardType

end
