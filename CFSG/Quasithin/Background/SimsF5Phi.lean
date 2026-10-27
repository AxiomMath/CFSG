module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP10Main
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP6
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP7
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8Rho
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP9

public section

namespace CFSG.Quasithin.SimsF5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431.U42Aut CFSG.CosetTable

section Conf


variable {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G} {z : G}

theorem toG_fhB_mem_imgG_That (c : AutCtx G M₁ M₂ z) : c.iso.toG fhB ∈ c.iso.imgG That :=
  (AutIso.mem_imgG c.iso).2 ⟨fhB, fhatA_mem_That, rfl⟩

theorem isGoodAt_toG_fhB (c : AutCtx G M₁ M₂ z) : c.IsGoodAt (c.iso.toG fhB) :=
  ⟨fhB, isGoodInv_fhatA, rfl⟩

theorem autCtx_conf (c : AutCtx G M₁ M₂ z) {R : Subgroup G}
    (hR : IsSylowTwoOf R (cenOf (c.iso.toG fhB)))
    (hTR : c.iso.imgG That ⊓ cenOf (c.iso.toG fhB) ≤ R) :
    Conf437 z (c.iso.toG fhB) (c.iso.imgG That) R ∧ Conf54 M₁ M₂ (c.iso.toG fhB) R ∧
      Conf55 c (c.iso.toG fhB) ∧
      (M₁ ⊔ M₂) ⊔ Subgroup.normalizer (aOf M₂ (c.iso.toG fhB) : Set G) = ⊤ := by
  have hT : IsSylowTwoOf (c.iso.imgG That) (M₁ ⊓ M₂) := isSylowTwoOf_imgG_That c.iso
  have hfT := toG_fhB_mem_imgG_That c
  have hgood := isGoodAt_toG_fhB c
  have hconf := u42AutInv u42AutSylow (u42AutNotExtremal u42AutSylow u42AutFusion) u42AutFusionZ
    G M₁ M₂ z c _ hT _ hfT hgood R hR hTR
  have h54 := u42AutF54 G M₁ M₂ z c _ hT _ hfT hgood R hR hTR hconf
  have h55 := u42AutF55 G M₁ M₂ z c _ hT _ hfT hgood R hR hTR hconf h54
  have h56 := u42AutF56 G M₁ M₂ z c _ hT _ hfT hgood R hR hTR hconf h54 h55
  exact ⟨hconf, h54, h55, h56⟩

theorem exists_R (c : AutCtx G M₁ M₂ z) :
    ∃ R : Subgroup G, IsSylowTwoOf R (cenOf (c.iso.toG fhB)) ∧
      c.iso.imgG That ⊓ cenOf (c.iso.toG fhB) ≤ R := by
  have hT : IsSylowTwoOf (c.iso.imgG That) (M₁ ⊓ M₂) := isSylowTwoOf_imgG_That c.iso
  have hTp : IsPGroup 2 ↥(c.iso.imgG That ⊓ cenOf (c.iso.toG fhB)) := hT.2.1.to_le inf_le_left
  exact A4.exists_isSylowTwoOf_ge (inf_le_right : c.iso.imgG That ⊓ cenOf (c.iso.toG fhB) ≤ _) hTp

theorem exists_rhoData (c : AutCtx G M₁ M₂ z) :
    ∃ d : RhoData G, Nat.card ↥d.H = 576 ∧ d.ι.range ⊔ d.H = ⊤ ∧ d.ι.range = M₁ ⊔ M₂ ∧
      (∀ x : P1h, d.ι (x : Ah) = (c.iso.phi1 x : G)) ∧
      (∀ x : P2h, d.ι (x : Ah) = (c.iso.phi2 x : G)) := by
  obtain ⟨R, hR, hTR⟩ := exists_R c
  obtain ⟨hconf, h54, h55, h56⟩ := autCtx_conf c hR hTR
  obtain ⟨hcF, hcF0, ι, hι1, hι2⟩ := h55
  obtain ⟨ρ, hρM, hρ2, hρe⟩ := u42AutRho G M₁ M₂ z c R hR hTR hconf h54 ⟨hcF, hcF0, ι, hι1, hι2⟩
    ι hι1 hι2
  let ιG : Ah →* G := (M₁ ⊔ M₂).subtype.comp ι.toMonoidHom
  have hinj : Function.Injective ιG := Subtype.val_injective.comp ι.injective
  have hFι : ιG fhatA = c.iso.toG fhB := iota_toG c ι hι1 fhB
  have hrange : ιG.range = M₁ ⊔ M₂ := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact (ι a).2
    · intro hx
      exact ⟨ι.symm ⟨x, hx⟩, by simp [ιG]⟩
  let d : RhoData G :=
    { ι := ιG
      ρ := ρ
      inj := hinj
      not_mem := by rw [hrange]; exact hρM
      sq := by rw [hFι]; exact hρ2
      conj := by
        intro a ha
        rw [hFι]
        exact hρe a ha }
  have hA : d.A = aOf M₂ (c.iso.toG fhB) := (aOf_eq_map c ι hι1).symm
  have hH : Nat.card ↥d.H = 576 := by
    have := h54.2.2.2.2.2.1
    change Nat.card ↥(Subgroup.normalizer (d.A : Set G)) = 576
    rw [hA]
    exact this
  have hG : d.ι.range ⊔ d.H = ⊤ := by
    show ιG.range ⊔ Subgroup.normalizer (d.A : Set G) = ⊤
    rw [hrange, hA]
    exact h56
  exact ⟨d, hH, hG, hrange, hι1, hι2⟩

end Conf

section Iso


theorem rhoData_toG_bijective {G : Type} [Group G] [Finite G] (d : RhoData G)
    (hH : Nat.card ↥d.H = 576) (hG : d.ι.range ⊔ d.H = ⊤) (hnt : ∃ g : G, g ≠ 1) :
    Function.Bijective (d.toG hH) := by
  have hsurj := d.toG_surjective hH hG
  have := isSimpleGroup_PG_p10
  have hker : (d.toG hH).ker = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (d.toG hH).ker with h | h
    · exact h
    · exfalso
      obtain ⟨a, ha⟩ := hnt
      obtain ⟨x, rfl⟩ := hsurj a
      exact ha (MonoidHom.mem_ker.1 (h ▸ Subgroup.mem_top x))
  exact ⟨(MonoidHom.ker_eq_bot_iff _).1 hker, hsurj⟩

theorem rhoData_iso {G : Type} [Group G] [Finite G] {G' : Type} [Group G'] [Finite G']
    (d : RhoData G) (hH : Nat.card ↥d.H = 576) (hG : d.ι.range ⊔ d.H = ⊤) (hnt : ∃ g : G, g ≠ 1)
    (d' : RhoData G') (hH' : Nat.card ↥d'.H = 576) (hG' : d'.ι.range ⊔ d'.H = ⊤)
    (hnt' : ∃ g : G', g ≠ 1) :
    ∃ Φ : G ≃* G', ∀ a : Ah, Φ (d.ι a) = d'.ι a := by
  let e : PG 7 p10Ws ≃* G := MulEquiv.ofBijective (d.toG hH) (rhoData_toG_bijective d hH hG hnt)
  let e' : PG 7 p10Ws ≃* G' :=
    MulEquiv.ofBijective (d'.toG hH') (rhoData_toG_bijective d' hH' hG' hnt')
  refine ⟨e.symm.trans e', fun a => ?_⟩
  have ha : a ∈ Subgroup.closure (Set.range fun i : Fin 6 => p10sA i) := by
    rw [closure_p10sA]; trivial
  refine Subgroup.closure_induction (p := fun a _ => (e.symm.trans e') (d.ι a) = d'.ι a)
    ?_ ?_ ?_ ?_ ha
  · rintro _ ⟨i, rfl⟩
    have h1 : d.ι (p10sA i) = d.toG hH (PresentedGroup.of (Fin.castLE (by omega : 6 ≤ 7) i)) := by
      rw [d.toG_of hH, d.gG_lt _ (by simp)]
      rfl
    have h2 : d'.ι (p10sA i) =
        d'.toG hH' (PresentedGroup.of (Fin.castLE (by omega : 6 ≤ 7) i)) := by
      rw [d'.toG_of hH', d'.gG_lt _ (by simp)]
      rfl
    rw [h1, h2, MulEquiv.trans_apply]
    have : e.symm (d.toG hH (PresentedGroup.of (Fin.castLE (by omega : 6 ≤ 7) i))) =
        PresentedGroup.of (Fin.castLE (by omega : 6 ≤ 7) i) :=
      e.symm_apply_apply (PresentedGroup.of (Fin.castLE (by omega : 6 ≤ 7) i))
    rw [this]
    rfl
  · simp only [map_one]
  · intro x y _ _ hx hy
    simp only [map_mul] at hx hy ⊢
    rw [hx, hy]
  · intro x _ hx
    simp only [map_inv] at hx ⊢
    rw [hx]

end Iso

section Main


theorem autCtx_iso {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G} {z : G}
    (c : AutCtx G M₁ M₂ z) {G' : Type} [Group G'] [Finite G'] {M₁' M₂' : Subgroup G'} {z' : G'}
    (c' : AutCtx G' M₁' M₂' z') :
    ∃ Φ : G ≃* G', (∀ x : P1h, Φ (c.iso.phi1 x : G) = (c'.iso.phi1 x : G')) ∧
      (∀ x : P2h, Φ (c.iso.phi2 x : G) = (c'.iso.phi2 x : G')) := by
  obtain ⟨d, hH, hG, -, h1, h2⟩ := exists_rhoData c
  obtain ⟨d', hH', hG', -, h1', h2'⟩ := exists_rhoData c'
  obtain ⟨Φ, hΦ⟩ := rhoData_iso d hH hG ⟨z, c.z1⟩ d' hH' hG' ⟨z', c'.z1⟩
  refine ⟨Φ, fun x => ?_, fun x => ?_⟩
  · rw [← h1, ← h1', hΦ]
  · rw [← h2, ← h2', hΦ]

end Main

end CFSG.Quasithin.SimsF5
