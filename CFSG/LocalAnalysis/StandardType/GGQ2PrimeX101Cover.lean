module

public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeRhoT
public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeX101CoverGroup
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCenter

public section

namespace CFSG.GGQ2Prime

open Subgroup CFSG.Open CFSG.Models CFSG.Fischer
open scoped commutatorElement
open CFSG.LieType.Steinberg.CentralExt.GriessClassical (psu_odd_row)
open CFSG.ClassicalGroups.Unitary (fam_PSU_simplicity)

theorem exists_lieModel_inf_centralizer_of_rhoT
    {G : Type} [Group G] {L : Subgroup G} {e : (L ⧸ center L) ≃* T46}
    {ρ : normalizer (L : Set G) →* Equiv.Perm (Fin 693)} (hρ : RhoTSpec e ρ) {z : G}
    (hz : z ∈ normalizer (L : Set G))
    (hC : LieModel ↥(T46 ⊓ centralizer ({ρ ⟨z, hz⟩} : Set (Equiv.Perm (Fin 693)))) .PSU 5 2 1) :
    ∃ X : Subgroup G, LieModel X .PSU 5 2 1 ∧ X ≤ L ⊓ centralizer ({z} : Set G) ∧
      (∀ h ∈ L ⊓ centralizer ({z} : Set G), ∃ c ∈ L ⊓ centralizer (L : Set G), ∃ y ∈ X,
        h = c * y) ∧
      ∀ c ∈ T46 ⊓ centralizer ({ρ ⟨z, hz⟩} : Set (Equiv.Perm (Fin 693))),
        ∃ l : L, (l : G) ∈ X ∧ (e (QuotientGroup.mk l) : Equiv.Perm (Fin 693)) = c := by
  set C₀ : Subgroup (Equiv.Perm (Fin 693)) :=
    T46 ⊓ centralizer ({ρ ⟨z, hz⟩} : Set (Equiv.Perm (Fin 693)))
  have hC' : StatedClassicalModel ↥C₀ .PSU 5 2 1 := by
    obtain ⟨-, hcl | ⟨h0, -⟩⟩ := hC
    · exact hcl
    · exact absurd h0 (by norm_num)
  have hperf : commutator ↥C₀ = ⊤ := (psu_odd_row hC' (by decide)).1
  obtain ⟨hnt, hsim⟩ := fam_PSU_simplicity ↥C₀ 5 2 1 hC'
  have hZC : Subgroup.center ↥C₀ = ⊥ := x101Cover_center_eq_bot hperf
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ↥L →* Equiv.Perm (Fin 693),
      ∀ l : ↥L, ψ l = (e (QuotientGroup.mk l) : Equiv.Perm (Fin 693)) :=
    ⟨T46.subtype.comp (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))),
      fun _ => rfl⟩
  have hψT : ∀ l : ↥L, ψ l ∈ T46 := fun l => by rw [hψ]; exact (e _).2
  have hψsurj : ∀ c ∈ T46, ∃ l : ↥L, ψ l = c := by
    intro c hc
    obtain ⟨q, hq⟩ := e.surjective ⟨c, hc⟩
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨l, (hψ l).trans (congrArg Subtype.val hq)⟩
  have hψker : ∀ l : ↥L, ψ l = 1 ↔ l ∈ Subgroup.center ↥L := fun l => by
    have h1 : ψ l = 1 ↔ e (QuotientGroup.mk l) = 1 := by
      rw [hψ]
      exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
    rw [h1, map_eq_one_iff e e.injective, QuotientGroup.eq_one_iff]
  obtain ⟨θ, hθ⟩ : ∃ θ : ↥L →* ↥L, ∀ l : ↥L, ((θ l : ↥L) : G) = z * (l : G) * z⁻¹ :=
    ⟨(L.normalizerMonoidHom ⟨z, hz⟩).toMonoidHom,
      fun l => Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨z, hz⟩ l⟩
  have hθψ : ∀ l : ↥L, ρ ⟨z, hz⟩ * ψ l * (ρ ⟨z, hz⟩)⁻¹ = ψ (θ l) := by
    intro l
    have hl : z * (l : G) * z⁻¹ ∈ L := by rw [← hθ l]; exact (θ l).2
    have hel : (⟨z * (l : G) * z⁻¹, hl⟩ : ↥L) = θ l := Subtype.ext (hθ l).symm
    simp only [hψ]
    rw [← hel]
    exact hρ.conj ⟨z, hz⟩ l hl
  have hcentψ : ∀ l : ↥L,
      ψ l ∈ Subgroup.centralizer ({ρ ⟨z, hz⟩} : Set (Equiv.Perm (Fin 693))) ↔ ψ (θ l) = ψ l := by
    intro l
    rw [Subgroup.mem_centralizer_singleton_iff, ← hθψ l, mul_inv_eq_iff_eq_mul]
    exact eq_comm
  have hPθ : ∀ p : ↥L, ψ p ∈ C₀ → ψ (θ p) = ψ p := fun p hp =>
    (hcentψ p).1 (Subgroup.mem_inf.1 hp).2
  have hθc : ∀ p : ↥L, ψ p ∈ C₀ → ∃ c ∈ Subgroup.center ↥L, θ p = c * p := by
    intro p hp
    refine ⟨θ p * p⁻¹, ?_, by group⟩
    rw [← hψker, map_mul, map_inv, hPθ p hp, mul_inv_cancel]
  have hθcomm : ∀ p q : ↥L, ψ p ∈ C₀ → ψ q ∈ C₀ → θ ⁅p, q⁆ = ⁅p, q⁆ := by
    intro p q hp hq
    obtain ⟨c, hc, hcp⟩ := hθc p hp
    obtain ⟨d, hd, hdq⟩ := hθc q hq
    rw [map_commutatorElement, hcp, hdq]
    exact x101Cover_commutator_central hc hd
  obtain ⟨P, hPdef⟩ : ∃ P : Subgroup ↥L, P = C₀.comap ψ := ⟨_, rfl⟩
  have hmemP : ∀ l : ↥L, l ∈ P ↔ ψ l ∈ C₀ := fun l => by rw [hPdef]; exact Iff.rfl
  have hPmap : P.map ψ = C₀ := by
    rw [hPdef, Subgroup.map_comap_eq, inf_eq_right]
    intro c hc
    exact MonoidHom.mem_range.2 (hψsurj c (Subgroup.mem_inf.1 hc).1)
  obtain ⟨Xl, hXl⟩ : ∃ Xl : Subgroup ↥L, Xl = ⁅P, P⁆ := ⟨_, rfl⟩
  have hXlmap : Xl.map ψ = C₀ := by
    rw [hXl, Subgroup.map_commutator, hPmap]
    exact (x101Cover_commutator_eq_top_iff C₀).1 hperf
  have hXlP : Xl ≤ P := by
    rw [hXl]
    refine Subgroup.commutator_le.2 fun p hp q hq => ?_
    rw [commutatorElement_def]
    exact P.mul_mem (P.mul_mem (P.mul_mem hp hq) (P.inv_mem hp)) (P.inv_mem hq)
  have hdecomp : ∀ p ∈ P, ∃ x ∈ Xl, ∃ c ∈ Subgroup.center ↥L, p = c * x := by
    intro p hp
    have hpX : ψ p ∈ Xl.map ψ := by rw [hXlmap]; exact (hmemP p).1 hp
    obtain ⟨x, hx, hxp⟩ := Subgroup.mem_map.1 hpX
    refine ⟨x, hx, p * x⁻¹, ?_, by group⟩
    rw [← hψker, map_mul, map_inv, hxp, mul_inv_cancel]
  have hPP : ⁅P, P⁆ ≤ ⁅Xl, Xl⁆ := by
    refine Subgroup.commutator_le.2 fun p hp q hq => ?_
    obtain ⟨x, hx, c, hc, rfl⟩ := hdecomp p hp
    obtain ⟨y, hy, d, hd, rfl⟩ := hdecomp q hq
    rw [x101Cover_commutator_central hc hd]
    exact Subgroup.commutator_mem_commutator hx hy
  have hXlcomm : ⁅Xl, Xl⁆ = Xl := by
    apply le_antisymm
    · exact (Subgroup.commutator_mono hXlP hXlP).trans hXl.symm.le
    · intro g hg
      exact hPP (by rw [← hXl]; exact hg)
  have hXlperf : commutator ↥Xl = ⊤ := (x101Cover_commutator_eq_top_iff Xl).2 hXlcomm
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ↥Xl →* ↥C₀, ∀ x : ↥Xl, (Ψ x : Equiv.Perm (Fin 693)) = ψ x :=
    ⟨(ψ.comp Xl.subtype).codRestrict C₀ fun x => (hmemP _).1 (hXlP x.2), fun _ => rfl⟩
  have hΨsurj : Function.Surjective Ψ := by
    intro c
    have hc : (c : Equiv.Perm (Fin 693)) ∈ Xl.map ψ := by rw [hXlmap]; exact c.2
    obtain ⟨x, hx, hxc⟩ := Subgroup.mem_map.1 hc
    exact ⟨⟨x, hx⟩, Subtype.ext ((hΨ ⟨x, hx⟩).trans hxc)⟩
  have hZ : Subgroup.center ↥Xl = Ψ.ker := by
    ext s
    rw [MonoidHom.mem_ker]
    constructor
    · intro hs
      have hcen : Ψ s ∈ Subgroup.center ↥C₀ := by
        rw [Subgroup.mem_center_iff]
        intro g
        obtain ⟨u, rfl⟩ := hΨsurj g
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hs u]
      rw [hZC] at hcen
      exact Subgroup.mem_bot.1 hcen
    · intro hs
      have h1 : ψ (s : ↥L) = 1 := by
        have h2 := hΨ s
        rw [hs] at h2
        exact h2.symm
      have hsL : (s : ↥L) ∈ Subgroup.center ↥L := (hψker _).1 h1
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_center_iff.1 hsL (g : ↥L))
  have eK : ↥Xl ⧸ Subgroup.center ↥Xl ≃* ↥C₀ :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans
      (QuotientGroup.quotientKerEquivOfSurjective Ψ hΨsurj)
  obtain ⟨a, b, hab⟩ := x101Cover_exists_noncomm (H := ↥C₀) hZC
  have hQS : CFSG.IsQuasisimple ↥Xl :=
    ⟨Group.IsPerfect.mk hXlperf, eK.isSimpleGroup,
      ⟨eK.symm a, eK.symm b, fun h => hab (by simpa using congrArg eK h)⟩⟩
  have hQL : CFSG.Blueprint.LieModel (↥Xl ⧸ Subgroup.center ↥Xl) .PSU 5 2 1 :=
    Or.inl ⟨by decide, x101Cover_classical_of_mulEquiv eK hC'⟩
  have hZ0 : Subgroup.center ↥Xl = ⊥ :=
    CFSG.OddStandard.SmallF3.HypA2Leaves.a2l_center_eq_bot_psu52 hQS hQL
  have hΨinj : Function.Injective Ψ := (MonoidHom.ker_eq_bot_iff Ψ).1 (hZ.symm.trans hZ0)
  have eX : ↥(Xl.map L.subtype) ≃* ↥C₀ :=
    (Subgroup.equivMapOfInjective Xl L.subtype Subtype.val_injective).symm.trans
      (MulEquiv.ofBijective Ψ ⟨hΨinj, hΨsurj⟩)
  have hXS : Xl ≤ (Subgroup.centralizer ({z} : Set G)).subgroupOf L := by
    rw [hXl]
    refine Subgroup.commutator_le.2 fun p hp q hq => ?_
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
    have hc : ((θ ⁅p, q⁆ : ↥L) : G) = ((⁅p, q⁆ : ↥L) : G) :=
      congrArg Subtype.val (hθcomm p q ((hmemP p).1 hp) ((hmemP q).1 hq))
    rw [hθ, mul_inv_eq_iff_eq_mul] at hc
    exact hc.symm
  refine ⟨Xl.map L.subtype, ⟨hC.1, Or.inl (x101Cover_classical_of_mulEquiv eX hC')⟩,
    ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hg
    exact Subgroup.mem_inf.2 ⟨x.2, Subgroup.mem_subgroupOf.1 (hXS hx)⟩
  · intro h hh
    obtain ⟨hhL, hhz⟩ := Subgroup.mem_inf.1 hh
    rw [Subgroup.mem_centralizer_singleton_iff] at hhz
    have hθh : θ ⟨h, hhL⟩ = ⟨h, hhL⟩ := Subtype.ext (by
      rw [hθ]
      show z * h * z⁻¹ = h
      rw [← hhz, mul_inv_cancel_right])
    have hPh : (⟨h, hhL⟩ : ↥L) ∈ P :=
      (hmemP _).2 (Subgroup.mem_inf.2 ⟨hψT ⟨h, hhL⟩, (hcentψ ⟨h, hhL⟩).2 (by rw [hθh])⟩)
    obtain ⟨x, hx, c, hc, hcx⟩ := hdecomp _ hPh
    refine ⟨(c : G), Subgroup.mem_inf.2 ⟨c.2, ?_⟩, (x : G),
      Subgroup.mem_map_of_mem L.subtype hx, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro m hm
      exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hc ⟨m, hm⟩)
    · exact congrArg Subtype.val hcx
  · intro c hc
    obtain ⟨x, hx, hxc⟩ := Subgroup.mem_map.1 (show c ∈ Xl.map ψ by rw [hXlmap]; exact hc)
    exact ⟨x, Subgroup.mem_map_of_mem L.subtype hx, (hψ x).symm.trans hxc⟩

end CFSG.GGQ2Prime
