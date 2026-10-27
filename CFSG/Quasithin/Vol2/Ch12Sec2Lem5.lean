module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem6
public import CFSG.LocalAnalysis.QuasithinUnique.CharTwoInheritance

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

namespace Lem5

variable {G : Type} [Group G]

theorem normalizer_le_normalizer_of_characteristic {S C : Subgroup G} (hCS : C ≤ S)
    (hchar : (C.subgroupOf S).Characteristic) :
    Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (C : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (S : Set G), ∀ c ∈ C, g * c * g⁻¹ ∈ C := by
    intro g hg c hc
    let φ : ↥S ≃* ↥S :=
      { toFun := fun s => ⟨g * s * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg s).mp s.2⟩
        invFun := fun s => ⟨g⁻¹ * s * g, by
          have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) s).mp s.2
          rwa [inv_inv] at this⟩
        left_inv := fun s => Subtype.ext (by simp [mul_assoc])
        right_inv := fun s => Subtype.ext (by simp [mul_assoc])
        map_mul' := fun s t => Subtype.ext (by simp [mul_assoc]) }
    have hmem : (⟨c, hCS hc⟩ : ↥S) ∈ C.subgroupOf S := hc
    have : φ.symm ⟨g * c * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg c).mp (hCS hc)⟩ ∈
        C.subgroupOf S := by
      have h1 : φ.symm ⟨g * c * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg c).mp (hCS hc)⟩ =
          ⟨c, hCS hc⟩ := Subtype.ext (by
        change g⁻¹ * (g * c * g⁻¹) * g = c
        group)
      rw [h1]
      exact hmem
    have h2 : (⟨g * c * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg c).mp (hCS hc)⟩ : ↥S) ∈
        (C.subgroupOf S).comap φ.symm.toMonoidHom := this
    rw [show (C.subgroupOf S).comap φ.symm.toMonoidHom = C.subgroupOf S from
      hchar.fixed φ.symm] at h2
    exact h2
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨fun hc => key g hg c hc, fun hc => ?_⟩
  have := key g⁻¹ (Subgroup.inv_mem _ hg) _ hc
  simpa [mul_assoc] using this

theorem centralizer_le_normalizer_zpowers (v : G) :
    Subgroup.centralizer ({v} : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers v : Subgroup G) : Set G) := by
  have h : Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G) =
      Subgroup.centralizer ({v} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [← h]
  exact Subgroup.centralizer_le_normalizer _

end Lem5

open Lem5

theorem stmt12_2_5_of (h1222 : Stmt12_2_2) (h323 : Stmt3_2_3) : Stmt12_2_5 := by
  intro G _ _ T L V hH v hv hv1
  have h1226 := stmt12_2_6_of h1222 h323
  obtain ⟨-, -, hall⟩ := ((h1222 G T hH.simple hH.nonabelian hH.qtke hH.sylow).resolve_left
    hH.notAlt) L hH.maximal hH.faithful hH.quasisimple
  obtain ⟨⟨hVT, -, -, -⟩, -, -, -, -⟩ := hall V hH.irrPlus
  obtain ⟨⟨hM2, -⟩, ⟨-, huniq⟩, -⟩ :=
    h323 G T L hH.simple hH.nonabelian hH.qtke hH.sylow hH.maximal hH.faithful hH.quasisimple
  rw [hH.conjClosure_eq] at hM2 huniq
  have hLM : L ≤ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer
  have hTM : T ≤ Subgroup.normalizer (L : Set G) := hH.normalizes
  have hvT : v ∈ T := hVT hv
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  ·
    exact (oTwoUpper_le _).trans (inf_le_inf_right _ hLM)
  ·
    refine le_trans ?_ (normalizer_le_normalizer_oTwoUpper _)
    intro x hx
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hx.1, Subgroup.le_normalizer hx.2⟩
  ·
    obtain ⟨S, hS⟩ := CFSG.Quasithin.exists_sylow_of_quasithinIsSylowTwo hH.sylow
    have hM : CharTwo (Subgroup.normalizer (L : Set G)) :=
      hH.qtke.2.1 _ hM2.1 ⟨S, hS ▸ hTM⟩
    have hz2 : IsPGroup 2 ↥(Subgroup.zpowers v) :=
      hH.sylow.1.to_le ((Subgroup.zpowers_le).mpr hvT)
    have h := hM.inf_centralizer ((Subgroup.zpowers_le).mpr (hTM hvT)) hz2
    rwa [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at h
  ·
    unfold cgsIn
    refine iSup₂_le fun C hCQ => iSup₂_le fun hC1 hchar => ?_
    have hC2 : IsPGroup 2 ↥C :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L ⊔ T)).to_le hCQ
    obtain ⟨M', hM', hCM'⟩ :=
      CFSG.Quasithin.exists_maxTwoLocal_ge (L := Subgroup.normalizer (C : Set G)) ⟨C, hC1, hC2, rfl⟩
    have hLTC : L ⊔ T ≤ Subgroup.normalizer (C : Set G) :=
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T)).trans
        (normalizer_le_normalizer_of_characteristic hCQ hchar)
    have hM'eq := huniq M' hM' (hLTC.trans hCM')
    intro x hx
    have hxM : x ∈ Subgroup.normalizer (L : Set G) := by
      rw [← hM'eq]
      exact hCM' hx.2
    exact ⟨hxM, hx.1⟩
  ·
    have hz1 : Subgroup.zpowers v ≠ ⊥ := by
      intro h
      apply hv1
      have : v ∈ Subgroup.zpowers v := Subgroup.mem_zpowers v
      rw [h, Subgroup.mem_bot] at this
      exact this
    have h := (h1226 G T L V hH).2 (Subgroup.zpowers v)
      (Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer ({v} : Set G)) hz1
      ((Subgroup.zpowers_le).mpr hv) (inf_le_right.trans (centralizer_le_normalizer_zpowers v))
    intro x hx
    have hx' : x ∈ (Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer ({v} : Set G)) ⊓
        Subgroup.normalizer (L : Set G) := ⟨hx, hx.1⟩
    rw [h] at hx'
    exact ⟨hx.1, hx'.2⟩

end CFSG.Quasithin.H13
