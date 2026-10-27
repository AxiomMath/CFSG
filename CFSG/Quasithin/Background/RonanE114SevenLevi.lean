module

public import CFSG.Quasithin.Vol2.Ch11SecU1L3IQ
public import CFSG.Quasithin.Vol2.Ch11SecU1L3IP
public import CFSG.Quasithin.Vol2.Ch11SecU1U3G

public section

namespace CFSG.Quasithin.RonanE114.Seven

open Matrix CFSG.Quasithin CFSG.Quasithin.E2P.Asc80 CFSG.Quasithin.Vol2.Ch11
open scoped MatrixGroups commutatorElement

section L3

open CFSG.Quasithin.Vol2.Ch11.SecU1.L3I

variable {p : ℕ} [Fact p.Prime]

theorem exists_levi_data_L3_core (hp5 : 5 ≤ p) {G : Type} [Group G]
    {L : Subgroup G} [L.Normal] (e : ↥L ≃* PSL3 p) {y : G} (hyL : y ∈ L)
    (hy2 : orderOf y = 2) :
    ∃ Y : Subgroup G, Y ≤ L ∧ Y ≤ Subgroup.centralizer ({y} : Set G) ∧
      Subgroup.centralizer ({y} : Set G) ≤ Subgroup.normalizer (Y : Set G) ∧
      Nonempty (↥Y ≃* SL(2, ZMod p)) ∧
      Group.IsSolvable ↥(L ⊓ Subgroup.centralizer (Y : Set G)) := by
  have hp2 : p ≠ 2 := by omega
  obtain ⟨e', he'⟩ := exists_equiv_zc hp2 e hyL hy2
  set f : PSL3 p →* G := L.subtype.comp e'.symm.toMonoidHom with hf
  have hfinj : Function.Injective f := L.subtype_injective.comp e'.symm.injective
  have hfz : f (zc p) = y := by
    rw [hf, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← he', MulEquiv.symm_apply_apply]
    rfl
  have hfL : ∀ c, f c ∈ L := fun c => (e'.symm c).2
  have hfe : ∀ (x : G) (hx : x ∈ L), f (e' ⟨x, hx⟩) = x := fun x hx => by
    rw [hf, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    rfl
  have hcomm_f : ∀ (x : G) (hx : x ∈ L) (c : PSL3 p),
      x * f c = f c * x ↔ e' ⟨x, hx⟩ * c = c * e' ⟨x, hx⟩ := by
    intro x hx c
    constructor
    · intro h
      apply hfinj
      rw [map_mul, map_mul, hfe x hx]
      exact h
    · intro h
      have h1 := congrArg f h
      rwa [map_mul, map_mul, hfe x hx] at h1
  have hCL : L ⊓ Subgroup.centralizer ({y} : Set G) = (leviC p).map f :=
    inf_centralizer_eq_map_leviC hp2 e' hyL he'
  set Y : Subgroup G := (leviY p).map f with hY
  have hYcomm : Y = ⁅L ⊓ Subgroup.centralizer ({y} : Set G),
      L ⊓ Subgroup.centralizer ({y} : Set G)⁆ := by
    rw [hCL, ← Subgroup.map_commutator, commutator_leviC hp5]
  have hYC0 : Y ≤ L ⊓ Subgroup.centralizer ({y} : Set G) := by
    rw [hCL]
    exact Subgroup.map_mono leviY_le_leviC
  have hCY : L ⊓ Subgroup.centralizer (Y : Set G) =
      (Subgroup.centralizer (leviY p : Set (PSL3 p))).map f := by
    ext x
    constructor
    · rintro ⟨hxL, hxY⟩
      refine ⟨e' ⟨x, hxL⟩, Subgroup.mem_centralizer_iff.mpr fun s hs => ?_, hfe x hxL⟩
      have h1 := Subgroup.mem_centralizer_iff.mp hxY (f s) ⟨s, hs, rfl⟩
      exact ((hcomm_f x hxL s).mp h1.symm).symm
    · rintro ⟨c, hc, rfl⟩
      refine ⟨hfL c, Subgroup.mem_centralizer_iff.mpr ?_⟩
      rintro _ ⟨s, hs, rfl⟩
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hc s hs]
  refine ⟨Y, hYC0.trans inf_le_left, hYC0.trans inf_le_right, fun n hn => ?_, ?_, ?_⟩
  ·
    rw [hYcomm]
    refine mem_normalizer_commutator ?_
    rw [Subgroup.mem_normalizer_iff]
    intro g
    have hgy : ∀ m ∈ Subgroup.centralizer ({y} : Set G), ∀ g ∈
        L ⊓ Subgroup.centralizer ({y} : Set G), m * g * m⁻¹ ∈
          L ⊓ Subgroup.centralizer ({y} : Set G) := by
      rintro m hm g ⟨hgL, hgy⟩
      exact ⟨(inferInstance : L.Normal).conj_mem g hgL m,
        Subgroup.mul_mem _ (Subgroup.mul_mem _ hm hgy) (Subgroup.inv_mem _ hm)⟩
    refine ⟨hgy n hn g, fun h => ?_⟩
    have := hgy n⁻¹ (Subgroup.inv_mem _ hn) _ h
    simpa [mul_assoc] using this
  ·
    have hrange : Y = (f.comp (ofSL2 p)).range := by rw [hY, MonoidHom.range_comp]; rfl
    have hinj : Function.Injective (f.comp (ofSL2 p)) := hfinj.comp (ofSL2_injective (p := p))
    exact ⟨(MulEquiv.subgroupCongr hrange).trans (MonoidHom.ofInjective hinj).symm⟩
  ·
    refine Group.isSolvable_of_comm fun a b => Subtype.ext ?_
    have ha : (a : G) ∈ (Subgroup.centralizer (leviY p : Set (PSL3 p))).map f := by
      rw [← hCY]
      exact a.2
    have hb : (b : G) ∈ (Subgroup.centralizer (leviY p : Set (PSL3 p))).map f := by
      rw [← hCY]
      exact b.2
    obtain ⟨c, hc, hca⟩ := ha
    obtain ⟨d, hd, hdb⟩ := hb
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hca, ← hdb, ← map_mul, ← map_mul,
      centralizer_leviY_comm hp2 hc hd]

theorem nParam_centralizer_le_one_L3
    (hp7 : 7 ≤ p) {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hAS : SecE3.AlmostSimple L) (e : ↥L ≃* PSL3 p) :
    ∀ x ∈ L, orderOf x = 2 → E1.nParam (Subgroup.centralizer ({x} : Set G)) ≤ 1 := by
  intro x hxL hx2
  haveI := hAS.normal
  obtain ⟨Y, -, hYC, hYn, ⟨eY⟩, hCs⟩ := exists_levi_data_L3_core (by omega) e hxL hx2
  exact nParam_centralizer_le_one_of_sl2 hAS hp7 hYC hYn eY hCs

end L3

section U3

open CFSG.Quasithin.Vol2.Ch11.SecU1.U3

variable {G : Type} [Group G] {L : Subgroup G} {p : ℕ} [Fact p.Prime] {F : Type} [Field F]
  [Finite F]

theorem exists_levi_data_U3_core (hp5 : 5 ≤ p) (hF : Nat.card F = p ^ 2)
    (hLn : L.Normal) (ψ : PSU3F p F ≃* ↥L) {y : G} (hyL : y ∈ L) (hy2 : orderOf y = 2) :
    ∃ Y : Subgroup G, Y ≤ L ∧ Y ≤ Subgroup.centralizer ({y} : Set G) ∧
      Subgroup.centralizer ({y} : Set G) ≤ Subgroup.normalizer (Y : Set G) ∧
      Nonempty (↥Y ≃* SL(2, ZMod p)) ∧
      Group.IsSolvable ↥(L ⊓ Subgroup.centralizer (Y : Set G)) := by
  have hp2 : p ≠ 2 := by omega
  obtain ⟨ψ', hψ'⟩ := exists_equiv_zcU hp2 hF ψ hyL hy2
  set f := embU ψ' with hf
  have hfinj : Function.Injective f := embU_injective ψ'
  have hCL : L ⊓ Subgroup.centralizer ({y} : Set G) = (leviCU hF).map f := by
    rw [← hψ', inf_centralizer_embU, centralizer_zcU hp2 hF]
  set Y : Subgroup G := (leviSL hF).map f with hY
  have hYcomm : Y = ⁅L ⊓ Subgroup.centralizer ({y} : Set G),
      L ⊓ Subgroup.centralizer ({y} : Set G)⁆ := by
    rw [hCL, ← Subgroup.map_commutator, commutator_leviCU hp5 hF]
  have hYC0 : Y ≤ L ⊓ Subgroup.centralizer ({y} : Set G) := by
    rw [hCL]
    exact Subgroup.map_mono (leviSL_le_leviCU hF)
  have hCY : L ⊓ Subgroup.centralizer (Y : Set G) =
      (Subgroup.centralizer (leviSL hF : Set (PSU3F p F))).map f :=
    inf_centralizer_map_embU ψ' (leviSL hF)
  refine ⟨Y, hYC0.trans inf_le_left, hYC0.trans inf_le_right, ?_, ?_, ?_⟩
  ·
    rw [hYcomm]
    exact CFSG.GorensteinWalter.le_normalizer_commutator_of_le_normalizer _ _ _
      (centralizer_le_normalizer_inf hLn y) (centralizer_le_normalizer_inf hLn y)
  ·
    exact ⟨((leviSL hF).equivMapOfInjective f hfinj).symm.trans (leviSLEquiv hF).symm⟩
  ·
    refine Group.isSolvable_of_comm fun a b => Subtype.ext ?_
    have ha : (a : G) ∈ (Subgroup.centralizer (leviSL hF : Set (PSU3F p F))).map f := by
      rw [← hCY]
      exact a.2
    have hb : (b : G) ∈ (Subgroup.centralizer (leviSL hF : Set (PSU3F p F))).map f := by
      rw [← hCY]
      exact b.2
    obtain ⟨c, hc, hca⟩ := ha
    obtain ⟨d, hd, hdb⟩ := hb
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hca, ← hdb, ← map_mul, ← map_mul,
      comm_of_mem_centralizer_leviSL hp2 hF hc hd]

theorem nParam_centralizer_le_one_U3
    [Finite G] (hp7 : 7 ≤ p) (hF : Nat.card F = p ^ 2)
    (hAS : SecE3.AlmostSimple L) (ψ : PSU3F p F ≃* ↥L) :
    ∀ x ∈ L, orderOf x = 2 → E1.nParam (Subgroup.centralizer ({x} : Set G)) ≤ 1 := by
  intro x hxL hx2
  obtain ⟨Y, -, hYC, hYn, ⟨e⟩, hCs⟩ := exists_levi_data_U3_core (by omega) hF hAS.normal ψ hxL hx2
  exact CFSG.Quasithin.Vol2.Ch11.SecU1.L3I.nParam_centralizer_le_one_of_sl2 hAS hp7 hYC hYn e hCs

end U3

end CFSG.Quasithin.RonanE114.Seven
