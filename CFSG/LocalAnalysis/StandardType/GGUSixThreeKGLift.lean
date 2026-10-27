module

public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylCompDefs
public import CFSG.LocalAnalysis.StandardType.GGUSixTwoLayer

public section

namespace CFSG.StandardType.UnitSixThreeKG

open CFSG CFSG.Assembly

open scoped commutatorElement

private theorem isCyclic_map_of_isCyclic {L' R : Type} [Group L'] [Group R] (P : Subgroup L')
    (hP : IsCyclic P) (ψ : L' →* R) : IsCyclic (P.map ψ) := by
  haveI : IsCyclic P := hP
  exact isCyclic_of_surjective (ψ.subgroupMap P) (MonoidHom.subgroupMap_surjective ψ P)

theorem exists_isPGroup_le_of_le_map {L' R : Type} [Group L'] [Finite L'] [Group R] (ψ : L' →* R)
    {X : Subgroup L'} {E : Subgroup R} (hE : E ≤ X.map ψ) (hE3 : IsPGroup 3 E) :
    ∃ P : Subgroup L', P ≤ X ∧ IsPGroup 3 P ∧ P.map ψ = E := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Y : Subgroup L' := X ⊓ E.comap ψ
  have hYmap : Y.map ψ = E := by
    refine le_antisymm ?_ ?_
    · rw [Subgroup.map_le_iff_le_comap]
      exact inf_le_right
    · rintro e he
      obtain ⟨x, hx, rfl⟩ := hE he
      exact ⟨x, ⟨hx, he⟩, rfl⟩
  obtain ⟨S⟩ : Nonempty (Sylow 3 ↥Y) := Sylow.nonempty
  refine ⟨(S : Subgroup ↥Y).map Y.subtype, ?_, ?_, ?_⟩
  · exact (Subgroup.map_subtype_le (H := Y) (S : Subgroup ↥Y)).trans inf_le_left
  · exact (S.isPGroup').map Y.subtype
  · let f : ↥Y →* ↥(Y.map ψ) := ψ.subgroupMap Y
    have hf : Function.Surjective f := MonoidHom.subgroupMap_surjective ψ Y
    have hE3' : IsPGroup 3 (Y.map ψ) := by
      rw [hYmap]
      exact hE3
    have htop : IsPGroup 3 (⊤ : Subgroup ↥(Y.map ψ)) := hE3'.to_subgroup ⊤
    have hSmap : (S : Subgroup ↥Y).map f = ⊤ := by
      have h := (S.mapSurjective hf).is_maximal' (Q := ⊤) htop le_top
      rw [Sylow.coe_mapSurjective] at h
      exact h.symm
    apply le_antisymm
    · rw [Subgroup.map_le_iff_le_comap]
      intro x hx
      rw [Subgroup.mem_comap]
      have hxY : x ∈ Y := Subgroup.map_subtype_le (H := Y) (S : Subgroup ↥Y) hx
      rw [← hYmap]
      exact ⟨x, hxY, rfl⟩
    · intro e he
      have heY : e ∈ Y.map ψ := hYmap.symm ▸ he
      obtain ⟨y, hy, rfl⟩ := heY
      have hmem : (⟨ψ y, ⟨y, hy, rfl⟩⟩ : ↥(Y.map ψ)) ∈ (S : Subgroup ↥Y).map f := by
        rw [hSmap]
        exact Subgroup.mem_top _
      obtain ⟨s, hs, hsf⟩ := hmem
      refine ⟨(s : L'), ⟨s, hs, rfl⟩, ?_⟩
      have hval : (f s : R) = ψ y := congrArg Subtype.val hsf
      simpa [f] using hval

theorem exists_lift_pgroup_other {L' R : Type} [Group L'] [Finite L'] [Group R] {ψ : L' →* R}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    {a : MulAut L'} {ab : MulAut R} (hc : ∀ l, ab (ψ l) = ψ (a l))
    {J₁ : Subgroup L'} (hJ₁ : IsComponentOf J₁ (ggFix a)) {Pb : Subgroup R} (hPb : IsPGroup 3 Pb)
    (hle : Pb ≤ ⨆ (B : Subgroup R) (_ : IsComponentOf B (ggFix ab) ∧ B ≠ J₁.map ψ ∧
      3 ∣ Nat.card B), B) :
    ∃ P : Subgroup L', IsPGroup 3 P ∧ P.map ψ = Pb ∧
      P ≤ ⨆ (J₂ : Subgroup L') (_ : IsComponentOf J₂ (ggFix a) ∧ J₂ ≠ J₁ ∧ 3 ∣ Nat.card J₂), J₂ := by
  classical
  let X : Subgroup L' := ⨆ (J₂ : Subgroup L')
    (_ : IsComponentOf J₂ (ggFix a) ∧ J₂ ≠ J₁ ∧ 3 ∣ Nat.card J₂), J₂
  have hPbX : Pb ≤ X.map ψ := by
    refine hle.trans (iSup_le fun B => iSup_le fun hB => ?_)
    obtain ⟨hBc, hBne, hB3⟩ := hB
    let J₂ : Subgroup L' := ⁅B.comap ψ, B.comap ψ⁆
    obtain ⟨hJ₂c, hJ₂map⟩ :=
      CFSG.StandardType.USixTwo.isComponentOf_lift_fix hψ hker hc hBc
    have hJ₂map' : J₂.map ψ = B := hJ₂map
    have hJ₂ne : J₂ ≠ J₁ := by
      intro heq
      apply hBne
      rw [← hJ₂map', heq]
    have hJ₂3 : 3 ∣ Nat.card J₂ := by
      have h3 : 3 ∣ Nat.card (J₂.map ψ) := by
        rw [hJ₂map']
        exact hB3
      exact h3.trans (Subgroup.card_map_dvd J₂ ψ)
    rw [← hJ₂map']
    exact Subgroup.map_mono (le_iSup₂ (f := fun J₂ (_ : IsComponentOf J₂ (ggFix a) ∧
      J₂ ≠ J₁ ∧ 3 ∣ Nat.card J₂) => J₂) J₂ ⟨hJ₂c, hJ₂ne, hJ₂3⟩)
  obtain ⟨P, hPX, hP3, hPmap⟩ := exists_isPGroup_le_of_le_map ψ hPbX hPb
  exact ⟨P, hP3, hPmap, hPX⟩

theorem not_ggFixCompCyclic_of_comp {L' R : Type} [Group L'] [Finite L'] [Group R] {ψ : L' →* R}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    {a : MulAut L'} {ab : MulAut R} (hc : ∀ l, ab (ψ l) = ψ (a l))
    (h : ∀ Jb : Subgroup R, IsComponentOf Jb (ggFix ab) → ∃ P : Subgroup R, IsPGroup 3 P ∧
      ¬ IsCyclic P ∧
      P ≤ ⨆ (B : Subgroup R) (_ : IsComponentOf B (ggFix ab) ∧ B ≠ Jb ∧ 3 ∣ Nat.card B), B) :
    ¬ GGFixCompCyclic 3 a := by
  intro hcyc
  unfold GGFixCompCyclic at hcyc
  obtain ⟨J₁, hJ₁, hcyc⟩ := hcyc
  have hJb : IsComponentOf (J₁.map ψ) (ggFix ab) :=
    CFSG.StandardType.USixTwo.isComponentOf_map_fix hψ hker hc hJ₁
  obtain ⟨Pb, hPb3, hPbnc, hPble⟩ := h (J₁.map ψ) hJb
  obtain ⟨P, hP3, hPmap, hPle⟩ := exists_lift_pgroup_other hψ hker hc hJ₁ hPb3 hPble
  have hPcyc : IsCyclic P := hcyc P hP3 hPle
  exact hPbnc (hPmap ▸ isCyclic_map_of_isCyclic P hPcyc ψ)

theorem ggFixCompCyclic_map {L' R : Type} [Group L'] [Finite L'] [Group R] {ψ : L' →* R}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    {a : MulAut L'} {ab : MulAut R} (hc : ∀ l, ab (ψ l) = ψ (a l))
    (h : GGFixCompCyclic 3 a) : GGFixCompCyclic 3 ab := by
  unfold GGFixCompCyclic at h ⊢
  obtain ⟨J₁, hJ₁, hcyc⟩ := h
  refine ⟨J₁.map ψ, CFSG.StandardType.USixTwo.isComponentOf_map_fix hψ hker hc hJ₁, ?_⟩
  intro Pb hPb3 hPble
  obtain ⟨P, hP3, hPmap, hPle⟩ := exists_lift_pgroup_other hψ hker hc hJ₁ hPb3 hPble
  have hPcyc : IsCyclic P := hcyc P hP3 hPle
  rw [← hPmap]
  exact isCyclic_map_of_isCyclic P hPcyc ψ

end CFSG.StandardType.UnitSixThreeKG

end
