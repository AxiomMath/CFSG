module

public import CFSG.Quasithin.H13.L32AC40c

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.CosetGeom

attribute [local instance] commGroupOfFact

theorem card_map_le' {A B : Type*} [Group A] [Group B] (f : A →* B) (S : Subgroup A)
    [Finite S] : Nat.card (S.map f) ≤ Nat.card S := by
  have h : S.map f = (f.comp S.subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [h]
  exact Nat.card_le_card_of_surjective _ (f.comp S.subtype).rangeRestrict_surjective

theorem card_range_le_index_mul {W : Type*} [Group W] [Finite W] (f : W →* W) (D : Subgroup W) :
    Nat.card f.range ≤ D.index * Nat.card (D.map f) := by
  have h1 := Subgroup.card_mul_index (D.map f.rangeRestrict)
  have h2 : (D.map f.rangeRestrict).index ∣ D.index :=
    Subgroup.index_map_dvd D f.rangeRestrict_surjective
  have h3 : Nat.card (D.map f.rangeRestrict) = Nat.card (D.map f) := by
    rw [← Subgroup.card_map_of_injective f.range.subtype_injective, Subgroup.map_map]
    rfl
  rw [h3] at h1
  rw [← h1, mul_comm]
  exact Nat.mul_le_mul_right _
    (Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) h2)

variable {G : Type} [Group G] [Finite G] {T L V H K : Subgroup G}

section Fact

variable [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure V H)))]

theorem card_range_commHom_phiU (hF : HypF918 T V L (fsuV1 T V) V H K) (x : ↥H) :
    Nat.card (A5Mod.commHom (phiU hF x)).range =
      (centralizerMod (fsuV1 T V) (conjClosure V H) (Subgroup.zpowers (x : G))).relIndex
        (conjClosure V H) := by
  rw [← Subgroup.index_ker]
  have hxH : Subgroup.zpowers (x : G) ≤ H := (Subgroup.zpowers_le).mpr x.2
  rw [← hF.toHypF98.toHypF91.relIndex_tilde_fixV hxH]
  congr 1
  ext w
  rw [MonoidHom.mem_ker, A5Mod.commHom_apply, mul_inv_eq_one, Subgroup.mem_subgroupOf,
    Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  have hw : (w : SecQuot (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V)) ∈
      tildeOf (fsuV1 T V) (conjClosure V H) := w.2
  have key : phiU hF x w = w ↔
      secMk (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V) ⟨x, hF.H_le_normalizer_V₁ x.2⟩ *
        (w : SecQuot _ _) = (w : SecQuot _ _) *
          secMk (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V)
            ⟨x, hF.H_le_normalizer_V₁ x.2⟩ := by
    rw [← Subtype.coe_inj, actH_apply_coe, mul_inv_eq_iff_eq_mul]
  rw [key]
  constructor
  · intro h
    refine ⟨hw, fun b hb => ?_⟩
    obtain ⟨y, hy, rfl⟩ := mem_secImg.mp hb
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hy' : y = ⟨x, hF.H_le_normalizer_V₁ x.2⟩ ^ n := Subtype.ext (by simpa using hn.symm)
    rw [hy', map_zpow]
    exact ((Commute.zpow_left h n))
  · rintro ⟨-, h⟩
    exact h _ (secMk_mem_secImg (A := Subgroup.normalizer (fsuV1 T V : Set G)) (B := fsuV1 T V)
      (x := ⟨x, hF.H_le_normalizer_V₁ x.2⟩) (Subgroup.mem_zpowers _))

omit [Finite G] [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure V H)))] in
theorem V₁_le_DH [Finite G] (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (S : Setting147 G T L V H) (hF : HypF918 T V L (fsuV1 T V) V H K)
    {γ γ' : F8.Geom T L H} {g : ↥((L ⊔ T) ⊔ H)} (s : F8Setup T V L H γ γ' g) :
    fsuV1 T V ≤ F8.DH V (fsuV1 T V) H (g : G) := by
  have hF98 := hF.toHypF98
  obtain ⟨-, -, -, hV12, -⟩ := stmtL32NModule_of_inputs h1332 h1334 G T L V S.hyp.hyp S.hyp.fsu
  have hHC : ∀ y ∈ H, ∀ z ∈ fsuV1 T V, y * z = z * y := by
    intro y hy z hz
    have h1 := hF.H_le_normalizer_V₁ hy
    rw [normalizer_eq_centralizer_of_card_eq_two hV12] at h1
    exact (Subgroup.mem_centralizer_iff.mp h1 z hz).symm
  have hA₁H : F8.A₁ (fsuV1 T V) (g : G) ≤ H := (hF98.A₁_le_Uγ (g := g)).trans (hF98.Uγ_le_H s)
  intro z hz
  refine ⟨le_conjClosure V H ((inf_le_left : fsuV1 T V ≤ V) hz), ?_, fun u hu => ?_⟩
  · rw [normalizer_eq_centralizer_of_card_eq_two (hF98.card_A₁ (g := g)),
      Subgroup.mem_centralizer_iff]
    intro a ha
    exact hHC a (hA₁H ha) z hz
  · have h1 := hHC u (hF98.Uγ_le_H s hu) z hz
    have e : z * u * z⁻¹ * u⁻¹ = 1 := by
      rw [← h1]
      group
    rw [e]
    exact (F8.A₁ (fsuV1 T V) (g : G)).one_mem

theorem card_map_commHom_DH_le (hF : HypF918 T V L (fsuV1 T V) V H K) {g : ↥((L ⊔ T) ⊔ H)}
    (hcomm : ⁅F8.Uγ V H (g : G), F8.DH V (fsuV1 T V) H (g : G)⁆ ≤ F8.A₁ (fsuV1 T V) (g : G))
    (hA₁ : Nat.card (F8.A₁ (fsuV1 T V) (g : G)) = 2) {x : ↥H}
    (hxU : (x : G) ∈ F8.Uγ V H (g : G)) :
    Nat.card (((tildeOf (fsuV1 T V) (F8.DH V (fsuV1 T V) H (g : G))).subgroupOf
      (tildeOf (fsuV1 T V) (conjClosure V H))).map (A5Mod.commHom (phiU hF x))) ≤ 2 := by
  set A₁ := F8.A₁ (fsuV1 T V) (g : G) with hA₁def
  set D := F8.DH V (fsuV1 T V) H (g : G) with hD
  have hUN : conjClosure V H ≤ Subgroup.normalizer (fsuV1 T V : Set G) :=
    hF.conjClosure_le_normalizer_V₁ (le_conjClosure V H)
  have hDU : D ≤ conjClosure V H := centralizerMod_le_left _ _ _
  set E := (tildeOf (fsuV1 T V) (A₁ ⊓ conjClosure V H)).subgroupOf
    (tildeOf (fsuV1 T V) (conjClosure V H)) with hE
  have hle : ((tildeOf (fsuV1 T V) D).subgroupOf (tildeOf (fsuV1 T V) (conjClosure V H))).map
      (A5Mod.commHom (phiU hF x)) ≤ E := by
    rintro _ ⟨w, hw, rfl⟩
    have hw' : ((w : ↥(tildeOf (fsuV1 T V) (conjClosure V H))) :
        SecQuot (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V)) ∈ tildeOf (fsuV1 T V) D := hw
    obtain ⟨d, hdD, hdw⟩ := mem_secImg.mp hw'
    rw [Subgroup.mem_subgroupOf, A5Mod.commHom_apply, Subgroup.coe_mul, Subgroup.coe_inv,
      actH_apply_coe, ← hdw]
    have hxd : (x : G) * d * (x : G)⁻¹ * (d : G)⁻¹ ∈ A₁ ⊓ conjClosure V H := by
      refine ⟨hcomm (Subgroup.commutator_mem_commutator hxU hdD), ?_⟩
      have h1 := (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V H x.2) d).mp
        (hDU hdD)
      exact (conjClosure V H).mul_mem h1 ((conjClosure V H).inv_mem (hDU hdD))
    have e : secMk (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V)
        ⟨x, hF.H_le_normalizer_V₁ x.2⟩ * secMk _ _ d *
        (secMk (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V)
          ⟨x, hF.H_le_normalizer_V₁ x.2⟩)⁻¹ * (secMk _ _ d)⁻¹ =
        secMk _ _ (⟨x, hF.H_le_normalizer_V₁ x.2⟩ * d * ⟨x, hF.H_le_normalizer_V₁ x.2⟩⁻¹ *
          d⁻¹) := by
      simp only [map_mul, map_inv]
    rw [e]
    exact secMk_mem_secImg (by simpa using hxd)
  calc Nat.card _ ≤ Nat.card E := Subgroup.card_le_of_le hle
    _ = Nat.card (tildeOf (fsuV1 T V) (A₁ ⊓ conjClosure V H)) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (secImg_mono inf_le_right)).toEquiv
    _ ≤ Nat.card ((A₁ ⊓ conjClosure V H).subgroupOf
        (Subgroup.normalizer (fsuV1 T V : Set G))) := card_map_le' _ _
    _ ≤ Nat.card A₁ := by
      let ι : ↥((A₁ ⊓ conjClosure V H).subgroupOf (Subgroup.normalizer (fsuV1 T V : Set G))) →
          ↥A₁ := fun a => ⟨((a : ↥(Subgroup.normalizer (fsuV1 T V : Set G))) : G), a.2.1⟩
      refine Nat.card_le_card_of_injective ι ?_
      intro a b hab
      have h1 := congrArg (fun z : ↥A₁ => (z : G)) hab
      exact Subtype.ext (Subtype.ext h1)
    _ = 2 := hA₁

end Fact

end CFSG.Quasithin.H13.L32A.C
