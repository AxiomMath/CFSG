module

public import CFSG.RankThree.PartOne.CTP.StrongPGlue

public section

namespace CFSG.RankThree.PartOne

open Subgroup

variable {G : Type*} [Group G] [Finite G] {p : ℕ} {M : Subgroup G}

theorem IsStronglyPEmbedded.centralizer_le_of_isPGroup [Fact p.Prime]
    {Y : Subgroup G} (hY : IsStronglyPEmbedded p Y) {Q : Subgroup G} (hQ : Q ≠ ⊥)
    (hQp : IsPGroup p Q) (hQY : Q ≤ Y) :
    Subgroup.centralizer (Q : Set G) ≤ Y :=
  (Subgroup.centralizer_le_normalizer (Q : Set G)).trans (hY.normalizer_le hQ hQp hQY)

theorem IsStronglyPEmbedded.normalizer_le_of_centralizer_le [Fact p.Prime]
    (hM : IsStronglyPEmbedded p M) {B : Subgroup G}
    (hC : Subgroup.centralizer (B : Set G) ≤ M)
    (hdvd : p ∣ Nat.card (Subgroup.centralizer (B : Set G))) :
    Subgroup.normalizer (B : Set G) ≤ M := by
  classical
  let C : Subgroup G := Subgroup.centralizer (B : Set G)
  let N : Subgroup G := Subgroup.normalizer (B : Set G)
  have hCM : C ≤ M := hC
  have hCN : C ≤ N := Subgroup.centralizer_le_normalizer (B : Set G)
  let C' : Subgroup N := C.subgroupOf N
  haveI : C'.Normal := by
    dsimp [C', C, N]
    rw [← Subgroup.normalizerMonoidHom_ker]
    exact MonoidHom.normal_ker _
  obtain ⟨R⟩ : Nonempty (Sylow p C') := inferInstance
  have hdvd' : p ∣ Nat.card C' := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCN).toEquiv]
    simpa [C] using hdvd
  have hRne : (R : Subgroup C') ≠ ⊥ := Sylow.ne_bot_of_dvd_card R hdvd'
  let R₁ : Subgroup N := (R : Subgroup C').map C'.subtype
  let R₀ : Subgroup G := R₁.map N.subtype
  have hR₀p : IsPGroup p R₀ := (R.isPGroup'.map C'.subtype).map N.subtype
  have hR₀ne : R₀ ≠ ⊥ := by
    intro h
    apply hRne
    have h₁ : R₁ = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective _ N.subtype_injective).mp h
    exact (Subgroup.map_eq_bot_iff_of_injective _ C'.subtype_injective).mp h₁
  have hR₀C : R₀ ≤ C := by
    rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (Subgroup.map_subtype_le (R : Subgroup C') hx)
  have hR₀M : R₀ ≤ M := hR₀C.trans hCM
  have hN₀ : Subgroup.normalizer (R₀ : Set G) ≤ M := hM.normalizer_le hR₀ne hR₀p hR₀M
  have hfr : Subgroup.normalizer (R₁ : Set N) ⊔ C' = ⊤ := by
    simpa [R₁] using Sylow.normalizer_sup_eq_top (G := N) (N := C') R
  intro n hn
  let nN : N := ⟨n, hn⟩
  have hnN : nN ∈ Subgroup.normalizer (R₁ : Set N) ⊔ C' := by
    rw [hfr]
    exact Subgroup.mem_top nN
  rcases (Subgroup.mem_sup_of_normal_right.mp hnN) with ⟨a, ha, c, hc, hac⟩
  have haG : (a : G) ∈ Subgroup.normalizer (R₀ : Set G) := by
    have h1 : (a : G) ∈ (Subgroup.normalizer (R₁ : Set N)).map N.subtype :=
      Subgroup.mem_map_of_mem N.subtype ha
    simpa [R₀] using (Subgroup.le_normalizer_map (H := R₁) (f := N.subtype) h1)
  have hcG : (c : G) ∈ C := Subgroup.mem_subgroupOf.mp hc
  have hn_eq : n = (a : G) * (c : G) := by
    have := congrArg N.subtype hac
    simpa [nN] using this.symm
  rw [hn_eq]
  exact M.mul_mem (hN₀ haG) (hCM hcG)

theorem IsStronglyPEmbedded.subgroupOf [Fact p.Prime] (hM : IsStronglyPEmbedded p M)
    {H : Subgroup G} (hH : ¬ H ≤ M) (hdvd : p ∣ Nat.card (H ⊓ M : Subgroup G)) :
    IsStronglyPEmbedded p ((H ⊓ M).subgroupOf H) := by
  refine ⟨fun htop => hH ((Subgroup.subgroupOf_eq_top.mp htop).trans inf_le_right), ?_, ?_⟩
  · rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : H ⊓ M ≤ H)).toEquiv]
  · rintro g hg hpdvd
    have hgM : (g : G) ∉ M := fun h =>
      hg (Subgroup.mem_subgroupOf.mpr ⟨g.2, h⟩)
    apply hM.2.2 (g : G) hgM
    have hle : (↑((H ⊓ M).subgroupOf H ⊓
        ((H ⊓ M).subgroupOf H).map (MulAut.conj g).toMonoidHom) : Subgroup H).map H.subtype ≤
        M ⊓ M.map (MulAut.conj (g : G)).toMonoidHom := by
      rintro _ ⟨y, ⟨hy1, ⟨y', hy', hyy'⟩⟩, rfl⟩
      refine ⟨(Subgroup.mem_subgroupOf.1 hy1).2, (y' : G),
        (Subgroup.mem_subgroupOf.1 hy').2, ?_⟩
      rw [← hyy']
      simp [MulAut.conj_apply]
    have hcard := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective H.subtype_injective] at hcard
    exact hpdvd.trans hcard

theorem IsStronglyPEmbedded.le_of_isPGroup_inf [Fact p.Prime]
    {Y P : Subgroup G} (hY : IsStronglyPEmbedded p Y) (hP : IsPGroup p P)
    (hne : P ⊓ Y ≠ ⊥) : P ≤ Y := by
  by_contra hPY
  let Q : Subgroup P := (P ⊓ Y).subgroupOf P
  have hQlt : Q < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro hQtop
    apply hPY
    intro x hxP
    have hxQ : (⟨x, hxP⟩ : P) ∈ Q := by
      rw [hQtop]
      exact Subgroup.mem_top _
    exact (Subgroup.mem_subgroupOf.mp hxQ).2
  let : Group.IsNilpotent P := hP.isNilpotent
  obtain ⟨y, hyN, hyQ⟩ :=
    SetLike.exists_of_lt (Group.normalizerCondition_of_isNilpotent Q hQlt)
  let R : Subgroup G := (Subgroup.normalizer (Q : Set P)).map P.subtype
  have hyR : (y : G) ∈ R := ⟨y, hyN, rfl⟩
  have hRN : R ≤ Subgroup.normalizer ((P ⊓ Y : Subgroup G) : Set G) := by
    rintro _ ⟨w, hw, rfl⟩
    have hw' : (w : P) ∈
        (Subgroup.normalizer ((P ⊓ Y : Subgroup G) : Set G)).subgroupOf P := by
      rw [Subgroup.subgroupOf_normalizer_eq inf_le_left]
      simpa [Q] using hw
    exact Subgroup.mem_subgroupOf.mp hw'
  have hQp : IsPGroup p ↥(P ⊓ Y) := hP.to_inf_left
  have hyY : (y : G) ∈ Y :=
    (hY.normalizer_le hne hQp inf_le_right) (hRN hyR)
  exact hyQ (Subgroup.mem_subgroupOf.mpr ⟨y.2, hyY⟩)

end CFSG.RankThree.PartOne
