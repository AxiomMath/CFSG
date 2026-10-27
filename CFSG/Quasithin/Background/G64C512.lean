module

public import CFSG.Quasithin.Background.G64C512Ext
public import CFSG.Quasithin.Background.C58Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedImage

public section

namespace CFSG.Quasithin.G64

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

section Internal

variable {G : Type} [Group G]

theorem mem_normalizer_of_forall {M : Type*} [Group M] [Finite M] {H : Subgroup M} {y : M}
    (h : ∀ x ∈ H, y * x * y⁻¹ ∈ H) : y ∈ Subgroup.normalizer (H : Set M) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  · rw [Subgroup.card_map_of_injective (MulAut.conj y).injective]

theorem conj_mem_centralizer {V : Subgroup G} {g c : G}
    (hg : g ∈ Subgroup.normalizer (V : Set G)) (hc : c ∈ Subgroup.centralizer (V : Set G)) :
    g * c * g⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro v hv
  have hv' : g⁻¹ * v * g ∈ V := by
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hg) v).1 hv
    simpa using this
  have h1 := hc _ hv'
  calc v * (g * c * g⁻¹) = g * ((g⁻¹ * v * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * v * g)) * g⁻¹ := by rw [h1]
    _ = g * c * g⁻¹ * v := by group

variable {V X : Subgroup G}

theorem map_commV_zpowers_rho (hV : IsElemAbelian 2 V) (hXN : X ≤ Subgroup.normalizer (V : Set G))
    (x : X) :
    (@commV V (commGroupOfElemAbelian hV)
        (Subgroup.zpowers (Setup.rho V X hXN x))).map V.subtype =
      ⁅V, Subgroup.zpowers (x : G)⁆ := by
  let _ : CommGroup V := commGroupOfElemAbelian hV
  have hcomm : ∀ u w : V, u * w = w * u := fun u w => by
    have := hV.1
    exact Subtype.ext (setLike_mul_comm u.2 w.2)
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap, G6.commV_le_iff]
    intro y hy v
    obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    rw [Subgroup.mem_comap, ← map_zpow]
    show ((Setup.rho V X hXN (x ^ z) v * v⁻¹ : V) : G) ∈ _
    rw [Subgroup.coe_mul, Setup.rho_apply_coe, Subgroup.coe_inv]
    have hmem : ⁅((x ^ z : X) : G), (v : G)⁆ ∈ ⁅Subgroup.zpowers (x : G), V⁆ :=
      Subgroup.commutator_mem_commutator (by simp) v.2
    rw [Subgroup.commutator_comm] at hmem
    simpa [commutatorElement_def] using hmem
  · rw [Subgroup.commutator_le]
    intro v hv y hy
    obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    set w : V := Setup.rho V X hXN (x ^ z) ⟨v, hv⟩⁻¹ * (⟨v, hv⟩⁻¹)⁻¹ with hw
    have hwmem : w ∈ @commV V (commGroupOfElemAbelian hV)
        (Subgroup.zpowers (Setup.rho V X hXN x)) := by
      have := G6.mem_commV_of_mem (Subgroup.zpow_mem_zpowers (Setup.rho V X hXN x) z)
        (⟨v, hv⟩⁻¹ : V)
      rwa [← map_zpow] at this
    refine ⟨w, hwmem, ?_⟩
    rw [hw, Subgroup.subtype_apply, Subgroup.coe_mul, Setup.rho_apply_coe, Subgroup.coe_inv,
      inv_inv]
    have hvx : ((x ^ z : X) : G) * (⟨v, hv⟩⁻¹ : V) * ((x ^ z : X) : G)⁻¹ ∈ V := by
      have := Setup.rho_apply_coe hXN (x ^ z) (⟨v, hv⟩⁻¹ : V)
      rw [← this]
      exact Subtype.mem _
    have hc := hcomm ⟨_, hvx⟩ ⟨v, hv⟩
    have hc' := congrArg Subtype.val hc
    simp only [Subgroup.coe_mul] at hc'
    rw [commutatorElement_def]
    simp only [Subgroup.coe_inv, SubgroupClass.coe_zpow] at hc' ⊢
    rw [hc']
    group

end Internal

theorem inputC512G64_of_lemmaG64 (h : LemmaG64) : C58.InputC512G64 := by
  intro G _ _ hsimple hnonab hqtke X V S a k hX2 hVred hS haS ha2 hcard hspan hkX hk3 hkV hinv
    hSk _
  have := hsimple
  have hXN : X ≤ Subgroup.normalizer (V : Set G) := hVred.2.1
  have hVe : IsElemAbelian 2 V := hVred.2.2.1
  let _ : CommGroup V := commGroupOfElemAbelian hVe
  have hV2 : ∀ v : V, v ^ 2 = 1 := fun v => Subtype.ext (hVe.2 v v.2)
  have haX : a ∈ X := hS.1 haS
  set ρ := Setup.rho V X hXN with hρ
  set a' := ρ ⟨a, haX⟩ with ha'
  set k' := ρ ⟨k, hkX⟩ with hk'
  have hmapc : ∀ x : X, Nat.card (commV (Subgroup.zpowers (ρ x))) =
      Nat.card ↥⁅V, Subgroup.zpowers (x : G)⁆ := by
    intro x
    rw [← map_commV_zpowers_rho hVe hXN x, Subgroup.card_map_of_injective V.subtype_injective]
  have hcard' : Nat.card (commV (Subgroup.zpowers a')) = 2 := by
    rw [ha', hmapc]
    exact hcard
  have ha'X : a' ∈ autOn X V := (Setup.mem_autOn_self_iff hXN).2 ⟨⟨a, haX⟩, rfl⟩
  have ha'1 : a' ≠ 1 := by
    intro h1
    rw [h1, Subgroup.zpowers_one_eq_bot] at hcard'
    have : commV (⊥ : Subgroup (MulAut V)) = ⊥ := by
      rw [eq_bot_iff, G6.commV_le_iff]
      intro x hx v
      rw [Subgroup.mem_bot] at hx
      rw [hx]
      simp
    rw [this, Subgroup.card_bot] at hcard'
    omega
  have ha'2 : a' ^ 2 = 1 := by
    rw [ha', ← map_pow]
    have : (⟨a, haX⟩ : X) ^ 2 = 1 := Subtype.ext (by simpa using ha2)
    rw [this, map_one]
  have hXsq : CFSG.SectionRank.IsSQTKCat X := (qtkeCore_of_cat hnonab hqtke).1 X hX2
  have hquot : IsQuotientOfSQTKCat ↥(autOn X V) := by
    refine ⟨↥X, inferInstance, inferInstance, ρ.ker, inferInstance, hXsq, ⟨?_⟩⟩
    exact (MulEquiv.subgroupCongr (Setup.range_rho hXN)).symm.trans
      (QuotientGroup.quotientKerEquivRange ρ).symm
  have hspan' : (⨆ (g : MulAut V) (_ : g ∈ autOn X V),
      (commV (Subgroup.zpowers a')).map g.toMonoidHom) = ⊤ := by
    set W := ⨆ (g : MulAut V) (_ : g ∈ autOn X V),
      (commV (Subgroup.zpowers a')).map g.toMonoidHom with hW
    have hle : conjClosure ⁅V, Subgroup.zpowers a⁆ X ≤ W.map V.subtype := by
      refine conjClosure_le fun x hx z hz => ?_
      rw [← map_commV_zpowers_rho hVe hXN ⟨a, haX⟩] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      refine ⟨ρ ⟨x, hx⟩ w, ?_, ?_⟩
      · refine (le_iSup₂_of_le (ρ ⟨x, hx⟩) ((Setup.mem_autOn_self_iff hXN).2 ⟨⟨x, hx⟩, rfl⟩)
          le_rfl : (commV (Subgroup.zpowers a')).map (ρ ⟨x, hx⟩).toMonoidHom ≤ W) ?_
        exact ⟨w, hw, rfl⟩
      · rw [Subgroup.subtype_apply, Setup.rho_apply_coe]
        rfl
    rw [hspan] at hle
    rw [eq_top_iff]
    intro v _
    obtain ⟨w, hw, hwv⟩ := hle v.2
    have : w = v := Subtype.ext hwv
    rwa [← this]
  have hyp : Hyp61 (autOn X V) a' :=
    { pCore_eq_bot := Setup.pCoreOf_autOn_eq_bot hVred
      quotient_sqtk := hquot
      mem := ha'X
      ne_one := ha'1
      sq_eq_one := ha'2
      card_comm_le := by rw [hcard']; norm_num
      span := hspan' }
  have hC := h ↥V hV2 (autOn X V) a' hyp hcard'
  have hS' : IsSylowTwoOf (autOn S V) (autOn X V) := Setup.isSylowTwoOf_autOn hS hXN
  have hk'X : k' ∈ autOn X V := (Setup.mem_autOn_self_iff hXN).2 ⟨⟨k, hkX⟩, rfl⟩
  have hk'1 : k' ≠ 1 := by
    intro h1
    exact hkV ((Setup.rho_eq_one_iff hXN ⟨k, hkX⟩).1 h1)
  have hk'3 : k' ^ 3 = 1 := by
    rw [hk', ← map_pow]
    have : (⟨k, hkX⟩ : X) ^ 3 = 1 := Subtype.ext (by simpa using hk3)
    rw [this, map_one]
  have hak' : a' * k' * a'⁻¹ * k' = 1 := by
    rw [ha', hk', ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    exact (Setup.rho_eq_one_iff hXN _).2 (by simpa using hinv)
  have hSk' : autOn S V ≤ Subgroup.normalizer (Subgroup.zpowers k' : Set (MulAut V)) := by
    refine le_normalizer_zpowers fun σ hσ => ?_
    obtain ⟨⟨s, hsX⟩, hsS, rfl⟩ := (Setup.mem_autOn_iff_rho hXN hS.1).1 hσ
    have h1 : s * k * s⁻¹ ∈ Subgroup.zpowers k ⊔ X ⊓ Subgroup.centralizer (V : Set G) :=
      (Subgroup.mem_normalizer_iff.1 (hSk hsS) k).1
        (Subgroup.mem_sup_left (Subgroup.mem_zpowers k))
    have hzn : Subgroup.zpowers k ≤
        Subgroup.normalizer ((X ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := by
      rw [Subgroup.zpowers_le]
      refine mem_normalizer_of_forall fun c hc => ⟨?_, ?_⟩
      · exact X.mul_mem (X.mul_mem hkX hc.1) (X.inv_mem hkX)
      · exact conj_mem_centralizer (hXN hkX) hc.2
    have h1' : s * k * s⁻¹ ∈
        ((Subgroup.zpowers k ⊔ X ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := h1
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hzn] at h1'
    obtain ⟨y, hy, c, hc, hyc⟩ := h1'
    obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    refine Subgroup.mem_zpowers_iff.2 ⟨z, ?_⟩
    have hcX : c ∈ X := hc.1
    have heq : (⟨s, hsX⟩ : X) * ⟨k, hkX⟩ * ⟨s, hsX⟩⁻¹ = ⟨k, hkX⟩ ^ z * ⟨c, hcX⟩ :=
      Subtype.ext (by simpa using hyc.symm)
    have hρc : ρ ⟨c, hcX⟩ = 1 := (Setup.rho_eq_one_iff hXN _).2 hc.2
    rw [hk', ← map_zpow, ← map_inv, ← map_mul, ← map_mul, heq, map_mul, hρc, mul_one]
  have hN := normalizer_sylow_le_of_conclusion hV2 hC ha'X ha'1 ha'2 hcard' hS' hk'X hk'1 hk'3
    hak' hSk'
  rintro g ⟨hgX, hgS⟩
  have hρgX : ρ ⟨g, hgX⟩ ∈ autOn X V := (Setup.mem_autOn_self_iff hXN).2 ⟨⟨g, hgX⟩, rfl⟩
  have hρgS : ρ ⟨g, hgX⟩ ∈ Subgroup.normalizer ((autOn S V : Subgroup (MulAut V)) :
      Set (MulAut V)) := by
    refine mem_normalizer_of_forall fun σ hσ => ?_
    obtain ⟨⟨s, hsX⟩, hsS, rfl⟩ := (Setup.mem_autOn_iff_rho hXN hS.1).1 hσ
    rw [← map_inv, ← map_mul, ← map_mul]
    refine (Setup.mem_autOn_iff_rho hXN hS.1).2 ⟨_, ?_, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 hgS s).1 hsS
  have h1 := hN ⟨hρgX, hρgS⟩
  rw [mem_normalizer_zpowers_iff] at h1
  refine mem_normalizer_of_forall fun y hy => ?_
  rw [← map_commV_zpowers_rho hVe hXN ⟨k, hkX⟩] at hy ⊢
  obtain ⟨w, hw, rfl⟩ := hy
  refine ⟨ρ ⟨g, hgX⟩ w, ?_, ?_⟩
  · have hle : Subgroup.zpowers (ρ ⟨g, hgX⟩ * k' * (ρ ⟨g, hgX⟩)⁻¹) ≤ Subgroup.zpowers k' := by
      rw [Subgroup.zpowers_le]
      exact h1
    have hmem : ρ ⟨g, hgX⟩ w ∈ commV (Subgroup.zpowers (ρ ⟨g, hgX⟩ * k' * (ρ ⟨g, hgX⟩)⁻¹)) := by
      rw [G6.commV_zpowers_conj]
      exact ⟨w, hw, rfl⟩
    exact G6.commV_mono hle hmem
  · rw [Subgroup.subtype_apply, Setup.rho_apply_coe]
    rfl

end CFSG.Quasithin.G64
