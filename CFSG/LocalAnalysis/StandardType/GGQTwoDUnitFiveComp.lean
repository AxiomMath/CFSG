module

public import CFSG.Assembly.LargeEvenDefs
public import CFSG.Foundations.Basic
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitCompA1
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitCompA2
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitCompB1

public section

namespace CFSG.StandardType.QTwo

theorem qtwoDU5_isComponent_of_isPComponent {Y : Type} [Group Y] [Finite Y]
    (hY : CFSG.pPrimeCore 3 Y = ⊥) {L : Subgroup Y} (hL : CFSG.IsPComponent 3 L) :
    CFSG.IsComponent L := by
  obtain ⟨K, hK, hLs, hLK, -⟩ := hL
  have hinj : Function.Injective (QuotientGroup.mk' (CFSG.pPrimeCore 3 Y)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hY]
  exact ⟨CFSG.IsQuasisimple.of_mulEquiv
    ((L.equivMapOfInjective _ hinj).trans (MulEquiv.subgroupCongr hLK)) hK.1, hLs⟩

theorem qtwoDU5_pLayer_le_normalizer {Y : Type} [Group Y] [Finite Y]
    (hY : CFSG.pPrimeCore 3 Y = ⊥) {A : Subgroup Y} (hA : CFSG.IsComponent A) :
    CFSG.pLayer Y 3 ≤ Subgroup.normalizer (A : Set Y) := by
  show sSup {L : Subgroup Y | CFSG.IsPComponent 3 L} ≤ _
  refine sSup_le fun L hL => ?_
  rcases CFSG.LocalCores.distinct_components_commute
      (qtwoDU5_isComponent_of_isPComponent hY hL) hA with rfl | h
  · exact Subgroup.le_normalizer
  · exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h).trans
      (Subgroup.centralizer_le_normalizer _)

private theorem qtwoDU5_map_conj_eq {Y : Type} [Group Y] {A : Subgroup Y} {g : Y}
    (hg : g ∈ Subgroup.normalizer (A : Set Y)) : A.map (MulAut.conj g).toMonoidHom = A := by
  ext z
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg a).mp ha
  · intro hz
    refine ⟨g⁻¹ * z * g, ?_, ?_⟩
    · have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) z).mp hz
      rwa [inv_inv] at h
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

theorem qtwoDU5_mem_center_of_commutator_mem_center {K : Type*} [Group K]
    (hK : commutator K = ⊤) (a : K) (h : ∀ b : K, a * b * a⁻¹ * b⁻¹ ∈ Subgroup.center K) :
    a ∈ Subgroup.center K := by
  let φ : K →* ↥(Subgroup.center K) :=
    { toFun := fun b => ⟨a * b * a⁻¹ * b⁻¹, h b⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro b c
        apply Subtype.ext
        have hc := Subgroup.mem_center_iff.mp (h c)
        simp only [Subgroup.coe_mul]
        calc a * (b * c) * a⁻¹ * (b * c)⁻¹
            = a * b * a⁻¹ * b⁻¹ * (b * (a * c * a⁻¹ * c⁻¹) * b⁻¹) := by group
          _ = a * b * a⁻¹ * b⁻¹ * ((a * c * a⁻¹ * c⁻¹) * b * b⁻¹) := by rw [hc b]
          _ = a * b * a⁻¹ * b⁻¹ * (a * c * a⁻¹ * c⁻¹) := by group }
  have hker : φ.ker = ⊤ := by
    rw [eq_top_iff, ← hK]
    exact Abelianization.commutator_subset_ker φ
  rw [Subgroup.mem_center_iff]
  intro b
  have hb : φ b = 1 := by
    have hmem : b ∈ φ.ker := hker ▸ Subgroup.mem_top b
    exact hmem
  have hb' : a * b * a⁻¹ * b⁻¹ = 1 := congrArg Subtype.val hb
  have : a * b = b * a := by
    calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
      _ = b * a := by rw [hb', one_mul]
  exact this.symm

variable {G : Type} [Group G] [Finite G]

theorem qtwoDU5_exists_component {H J : Subgroup G} {y : ↥H} (hy3 : y ^ 3 = 1)
    (hc : CFSG.Assembly.IsComponentOf J (H ⊓ Subgroup.centralizer ({(y : G)} : Set G)))
    (hl : J ≤ CFSG.Assembly.LargeEvenPLayer 3 H)
    (h3 : 3 ∣ Nat.card (↥(J.subgroupOf H) ⧸ Subgroup.center ↥(J.subgroupOf H)))
    (hyN : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H) y ∈
      CFSG.pLayer (↥H ⧸ CFSG.pPrimeCore 3 ↥H) 3 ⊔
        Subgroup.center (↥H ⧸ CFSG.pPrimeCore 3 ↥H)) :
    ∃ Q : Subgroup (↥H ⧸ CFSG.pPrimeCore 3 ↥H), CFSG.IsComponent Q ∧
      (J.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H)) ≤ Q := by
  let R : Subgroup ↥H := CFSG.pPrimeCore 3 ↥H
  let π : ↥H →* (↥H ⧸ R) := QuotientGroup.mk' R
  let τ : ↥H ⧸ R := π y
  obtain ⟨-, hJC, -, hcomp⟩ := qtwoDB7_transfer hc
  obtain ⟨hpc, -⟩ := qtwoDB7_image_isPCompIn (X := ↥H) hy3 hJC hcomp h3
  have hlay : (J.subgroupOf H).map π ≤ CFSG.pLayer (↥H ⧸ R) 3 :=
    (Subgroup.map_mono (qtwoDB7_le_pLayer hl)).trans (qtwoDB7_map_pLayer_le (X := ↥H))
  have hY : CFSG.pPrimeCore 3 (↥H ⧸ R) = ⊥ := qtwoDB7_pPrimeCore_quotient (X := ↥H)
  have hτ : τ ^ 3 = 1 := by
    change (π y) ^ 3 = 1
    rw [← map_pow, hy3, map_one]
  rcases qtwoDB7_single_or_diag hY hτ hpc hlay with ⟨Q, hQ, hJQ⟩ | ⟨A, hA, h01, -, -, -⟩
  · exact ⟨Q, hQ, hJQ⟩
  · exfalso
    have hle : CFSG.pLayer (↥H ⧸ R) 3 ⊔ Subgroup.center (↥H ⧸ R) ≤
        Subgroup.normalizer (A : Set (↥H ⧸ R)) :=
      sup_le (qtwoDU5_pLayer_le_normalizer hY hA)
        ((Subgroup.center_le_centralizer (A : Set (↥H ⧸ R))).trans
          (Subgroup.centralizer_le_normalizer _))
    exact h01 (qtwoDU5_map_conj_eq (hle hyN)).symm

theorem qtwoDU5_one_component {H J₁ J₂ P : Subgroup G} {y₁ y₂ : ↥H}
    (hy₁3 : y₁ ^ 3 = 1) (hy₂3 : y₂ ^ 3 = 1)
    (hc₁ : CFSG.Assembly.IsComponentOf J₁ (H ⊓ Subgroup.centralizer ({(y₁ : G)} : Set G)))
    (hc₂ : CFSG.Assembly.IsComponentOf J₂ (H ⊓ Subgroup.centralizer ({(y₂ : G)} : Set G)))
    (hl₁ : J₁ ≤ CFSG.Assembly.LargeEvenPLayer 3 H) (hl₂ : J₂ ≤ CFSG.Assembly.LargeEvenPLayer 3 H)
    (h3₁ : 3 ∣ Nat.card (↥(J₁.subgroupOf H) ⧸ Subgroup.center ↥(J₁.subgroupOf H)))
    (h3₂ : 3 ∣ Nat.card (↥(J₂.subgroupOf H) ⧸ Subgroup.center ↥(J₂.subgroupOf H)))
    (hyN₁ : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H) y₁ ∈
      CFSG.pLayer (↥H ⧸ CFSG.pPrimeCore 3 ↥H) 3 ⊔
        Subgroup.center (↥H ⧸ CFSG.pPrimeCore 3 ↥H))
    (hyN₂ : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H) y₂ ∈
      CFSG.pLayer (↥H ⧸ CFSG.pPrimeCore 3 ↥H) 3 ⊔
        Subgroup.center (↥H ⧸ CFSG.pPrimeCore 3 ↥H))
    (hP₁ : P ≤ J₁) (hP₂ : P ≤ J₂) (hPJ : ∃ a ∈ P, ∃ b ∈ J₁, a * b ≠ b * a) :
    ∃ N : Subgroup G, CFSG.Assembly.LargeEvenPComponent 3 H N ∧ J₁ ≤ N ∧ J₂ ≤ N := by
  let R : Subgroup ↥H := CFSG.pPrimeCore 3 ↥H
  let π : ↥H →* (↥H ⧸ R) := QuotientGroup.mk' R
  obtain ⟨hJH₁, -, hq₁, -⟩ := qtwoDB7_transfer hc₁
  obtain ⟨hJH₂, -, hq₂, -⟩ := qtwoDB7_transfer hc₂
  obtain ⟨Q₁, hQ₁, hJQ₁⟩ := qtwoDU5_exists_component hy₁3 hc₁ hl₁ h3₁ hyN₁
  obtain ⟨Q₂, hQ₂, hJQ₂⟩ := qtwoDU5_exists_component hy₂3 hc₂ hl₂ h3₂ hyN₂
  have hQeq : Q₁ = Q₂ := by
    by_contra hne
    have hcomm : ⁅Q₁, Q₂⁆ = ⊥ :=
      (CFSG.LocalCores.distinct_components_commute hQ₁ hQ₂).resolve_left hne
    obtain ⟨a, ha, b, hb, hab⟩ := hPJ
    apply hab
    set aH : ↥H := ⟨a, hJH₁ (hP₁ ha)⟩ with haH
    have hJ₁c : ∀ jH : ↥H, (jH : G) ∈ J₁ → aH * jH * aH⁻¹ * jH⁻¹ ∈ R := by
      intro jH hj
      have haQ : π aH ∈ Q₂ := hJQ₂ ⟨aH, Subgroup.mem_subgroupOf.mpr (hP₂ ha), rfl⟩
      have hjQ : π jH ∈ Q₁ := hJQ₁ ⟨jH, Subgroup.mem_subgroupOf.mpr hj, rfl⟩
      have hc : π aH * π jH = π jH * π aH :=
        Subgroup.mem_centralizer_iff.mp
          ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm) hjQ) (π aH) haQ
      refine (QuotientGroup.eq_one_iff _).mp ?_
      change π (aH * jH * aH⁻¹ * jH⁻¹) = 1
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc]
      group
    let K : Subgroup ↥H := J₁.subgroupOf H
    have hKperf : commutator ↥K = ⊤ := hq₁.1.commutator_eq_top
    have hcore := qtwoDB7_inf_core_le_center (X := ↥H) hq₁ h3₁
    let a' : ↥K := ⟨aH, Subgroup.mem_subgroupOf.mpr (hP₁ ha)⟩
    have hcent : a' ∈ Subgroup.center ↥K := by
      refine qtwoDU5_mem_center_of_commutator_mem_center hKperf a' fun k => hcore ?_
      rw [Subgroup.mem_subgroupOf]
      refine ⟨(a' * k * a'⁻¹ * k⁻¹).2, ?_⟩
      have hk := hJ₁c (k : ↥H) (Subgroup.mem_subgroupOf.mp k.2)
      simpa [a'] using hk
    have hba := Subgroup.mem_center_iff.mp hcent
      ⟨⟨b, hJH₁ hb⟩, Subgroup.mem_subgroupOf.mpr hb⟩
    have h' := congrArg (fun z : ↥K => ((z : ↥H) : G)) hba
    simp only [Subgroup.coe_mul, a', haH] at h'
    exact h'.symm
  obtain ⟨N₁, hN₁, hJN₁, himg₁⟩ := qtwoDB7_exists_pcomp hQ₁ hJH₁ hq₁ h3₁ hJQ₁
  obtain ⟨N₂, hN₂, hJN₂, himg₂⟩ := qtwoDB7_exists_pcomp hQ₂ hJH₂ hq₂ h3₂ hJQ₂
  have hN₁₂ : N₁ = N₂ := qtwoDB7_pcomp_unique hN₁ hN₂ (himg₁.trans (hQeq.trans himg₂.symm))
  exact ⟨N₁, hN₁, hJN₁, hN₁₂.symm ▸ hJN₂⟩

end CFSG.StandardType.QTwo

end
