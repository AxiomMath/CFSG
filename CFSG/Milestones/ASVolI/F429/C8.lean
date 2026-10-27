module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Milestones.ASVolI.F4

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam
  CFSG.Quasithin.RankTwoAmalgam.Completion

section Generic

variable {G : Type} [Group G]

theorem burnsideF429_oTwoRes_mono {A B : Subgroup G} (h : A ≤ B) : oTwoRes A ≤ oTwoRes B :=
  Subgroup.closure_mono fun _ hx => ⟨h hx.1, hx.2⟩

theorem burnsideF429_perfectCore_le_oTwoRes [Finite G] (P : Subgroup G) :
    perfectCore P ≤ oTwoRes P := by
  have hOP : oTwoRes P ≤ P := oTwoRes_le P
  haveI hN : ((oTwoRes P).subgroupOf P).Normal := ⟨fun n hn k => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hc : (k : G) * n * (k : G)⁻¹ ∈ (oTwoRes P).map (MulAut.conj (k : G)).toMonoidHom :=
      ⟨n, hn, rfl⟩
    have hmap : (oTwoRes P).map (MulAut.conj (k : G)).toMonoidHom ≤ oTwoRes P := by
      unfold oTwoRes
      rw [MonoidHom.map_closure]
      refine Subgroup.closure_mono ?_
      rintro _ ⟨y, ⟨hyP, m, hm, hym⟩, rfl⟩
      refine ⟨P.mul_mem (P.mul_mem k.2 hyP) (P.inv_mem k.2), m, hm, ?_⟩
      rw [← map_pow, hym, map_one]
    exact hmap hc⟩
  have hp : IsPGroup 2 (↥P ⧸ (oTwoRes P).subgroupOf P) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      haveI : Finite ↥P := inferInstance
      obtain ⟨n, hn⟩ : ∃ n : ℕ, 0 < n ∧ (x : ↥P) ^ n = 1 :=
        ⟨orderOf x, orderOf_pos x, pow_orderOf_eq_one x⟩
      obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      refine Subgroup.subset_closure ⟨(x ^ 2 ^ k).2, m, hm, ?_⟩
      rw [← Subgroup.coe_pow, ← pow_mul, ← hkm, pow_orderOf_eq_one]
      rfl
  have hsolv : Group.IsSolvable (↥P ⧸ (oTwoRes P).subgroupOf P) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI := hp.isNilpotent
    infer_instance
  obtain ⟨n, hn⟩ := (isSolvable_def (G := ↥P ⧸ (oTwoRes P).subgroupOf P)).1 hsolv
  intro x hx
  have h2 := perfectCore_le_derivedSeriesOf P n hx
  rw [derivedSeriesOf_eq_map_derivedSeries] at h2
  obtain ⟨y, hy, rfl⟩ := h2
  have h1 := map_derivedSeries_le_derivedSeries (QuotientGroup.mk' ((oTwoRes P).subgroupOf P)) n
    ⟨y, hy, rfl⟩
  rw [hn, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact Subgroup.mem_subgroupOf.1 h1

end Generic

section Completion

variable {E : Type} [Group E] {M₁ M₂ : Subgroup E} {Y : Type} [Group Y]

theorem burnsideF429_f1_α1_eq_f2_α2 (β : Cpl M₁ M₂ Y) (x : ↥(M₁ ⊓ M₂)) :
    f1 (c := β) ((RankTwoAmalgam.ofSubgroups M₁ M₂).α1 x) =
      f2 (c := β) ((RankTwoAmalgam.ofSubgroups M₁ M₂).α2 x) :=
  Subtype.ext ((β.comm1 x).trans (β.comm2 x).symm)

theorem burnsideF429_map_oTwoRes_le {M P : Subgroup E} {H : Type} [Group H] (g : ↥M →* H)
    {X : Subgroup H} (hX : ((P ⊓ M).subgroupOf M).map g ≤ X) {z : E}
    (hz : z ∈ oTwoRes (P ⊓ M)) (hzM : z ∈ M) : g ⟨z, hzM⟩ ∈ oTwoRes X := by
  have key : ∀ z, ∀ _ : z ∈ oTwoRes (P ⊓ M), ∀ hzM : z ∈ M, g ⟨z, hzM⟩ ∈ oTwoRes X := by
    intro z hz
    induction hz using Subgroup.closure_induction with
    | mem x hx =>
      intro hxM
      obtain ⟨hxG, m, hm, hxm⟩ := hx
      refine Subgroup.subset_closure ⟨hX ⟨⟨x, hxM⟩, hxG, rfl⟩, m, hm, ?_⟩
      have hpow : (⟨x, hxM⟩ : ↥M) ^ m = 1 := Subtype.ext hxm
      rw [← map_pow, hpow, map_one]
    | one =>
      intro h1
      have e : (⟨1, h1⟩ : ↥M) = 1 := rfl
      rw [e, map_one]
      exact Subgroup.one_mem _
    | mul x y hx hy ihx ihy =>
      intro hxyM
      have hxM : x ∈ M := ((oTwoRes_le _) hx).2
      have hyM : y ∈ M := ((oTwoRes_le _) hy).2
      have e : (⟨x * y, hxyM⟩ : ↥M) = ⟨x, hxM⟩ * ⟨y, hyM⟩ := rfl
      rw [e, map_mul]
      exact Subgroup.mul_mem _ (ihx hxM) (ihy hyM)
    | inv x hx ih =>
      intro hxM
      have hxM' : x ∈ M := ((oTwoRes_le _) hx).2
      have e : (⟨x⁻¹, hxM⟩ : ↥M) = (⟨x, hxM'⟩ : ↥M)⁻¹ := rfl
      rw [e, map_inv]
      exact Subgroup.inv_mem _ (ih hxM')
  exact key z hz hzM

theorem burnsideF429_c8_map_le (Gp : Subgroup E) (β : Cpl M₁ M₂ Y) {A : Subgroup E}
    (hA : A ≤ ((M₁ ⊓ M₂) ⊓ oTwoRes (Gp ⊓ M₁)) ⊔ ((M₁ ⊓ M₂) ⊓ oTwoRes (Gp ⊓ M₂))) :
    (A.subgroupOf (M₁ ⊓ M₂)).map (bmap β) ≤
      oTwoRes (((Gp ⊓ M₁).subgroupOf M₁).map (f1 (c := β)) ⊔
        ((Gp ⊓ M₂).subgroupOf M₂).map (f2 (c := β))) := by
  have hle : A.subgroupOf (M₁ ⊓ M₂) ≤
      ((M₁ ⊓ M₂) ⊓ oTwoRes (Gp ⊓ M₁)).subgroupOf (M₁ ⊓ M₂) ⊔
        ((M₁ ⊓ M₂) ⊓ oTwoRes (Gp ⊓ M₂)).subgroupOf (M₁ ⊓ M₂) := by
    rw [← Subgroup.subgroupOf_sup inf_le_left inf_le_left]
    exact fun x hx => hA hx
  refine (Subgroup.map_mono hle).trans ?_
  rw [Subgroup.map_sup]
  refine sup_le ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    have hx' := (Subgroup.mem_subgroupOf.1 hx).2
    exact burnsideF429_map_oTwoRes_le (f1 (c := β)) le_sup_left hx' _
  · rintro _ ⟨x, hx, rfl⟩
    have hx' := (Subgroup.mem_subgroupOf.1 hx).2
    have e := burnsideF429_f1_α1_eq_f2_α2 β x
    change f1 (c := β) ((RankTwoAmalgam.ofSubgroups M₁ M₂).α1 x) ∈ _
    exact e ▸ burnsideF429_map_oTwoRes_le (f2 (c := β)) le_sup_right hx' _

theorem burnsideF429_Sp_eq (Gp : Subgroup E) (β : Cpl M₁ M₂ Y) :
    Sp 2 Gp β = ((pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))).subgroupOf (M₁ ⊓ M₂)).map (bmap β) := by
  unfold Sp bmap
  exact Subgroup.map_map _ _ _

theorem burnsideF429_bmap_injective (β : Cpl M₁ M₂ Y) (hβ : β.IsFaithful) :
    Function.Injective (bmap β) := by
  intro a b hab
  have h1 : β.φ1 ((RankTwoAmalgam.ofSubgroups M₁ M₂).α1 a) =
      β.φ1 ((RankTwoAmalgam.ofSubgroups M₁ M₂).α1 b) := congrArg Subtype.val hab
  exact (RankTwoAmalgam.ofSubgroups_isInjective M₁ M₂).1 (hβ.1 h1)

end Completion

section Clause

variable {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

theorem burnsideF429_c8_of {κ : GLKind} {f : ℕ}
    (ha : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ⊓ oTwoRes Gp ≤
      ((M₁ ⊓ M₂) ⊓ oTwoRes (Gp ⊓ M₁)) ⊔ ((M₁ ⊓ M₂) ⊓ oTwoRes (Gp ⊓ M₂)))
    (hb : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤
        ((M₁ ⊓ M₂) ⊓ oTwoRes (Gp ⊓ M₁)) ⊔ ((M₁ ⊓ M₂) ⊓ oTwoRes (Gp ⊓ M₂)) ∨
      (f = 1 ∧ (κ = .Sp4 ∨ κ = .G2 ∨ κ = .F4tw) ∧
        (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ⊓ oTwoRes Gp).relIndex (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) ∣ 2)) :
    ∀ (Y : Type) [Group Y] (β : Cpl M₁ M₂ Y), β.IsFaithful →
      ((pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ⊓ oTwoRes Gp).subgroupOf (M₁ ⊓ M₂)).map (bmap β) ≤
          oTwoRes (((Gp ⊓ M₁).subgroupOf M₁).map (f1 (c := β)) ⊔
            ((Gp ⊓ M₂).subgroupOf M₂).map (f2 (c := β))) ∧
        (Sp 2 Gp β ≤ oTwoRes (((Gp ⊓ M₁).subgroupOf M₁).map (f1 (c := β)) ⊔
              ((Gp ⊓ M₂).subgroupOf M₂).map (f2 (c := β))) ∨
          (f = 1 ∧ (κ = .Sp4 ∨ κ = .G2 ∨ κ = .F4tw) ∧
            (Sp 2 Gp β ⊓ oTwoRes (((Gp ⊓ M₁).subgroupOf M₁).map (f1 (c := β)) ⊔
              ((Gp ⊓ M₂).subgroupOf M₂).map (f2 (c := β)))).relIndex (Sp 2 Gp β) = 2)) := by
  intro Y _ β hβ
  have h1 := burnsideF429_c8_map_le Gp β ha
  refine ⟨h1, ?_⟩
  rcases hb with hb | ⟨hf, hκ, hdvd⟩
  · left
    rw [burnsideF429_Sp_eq]
    exact burnsideF429_c8_map_le Gp β hb
  · set S := pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) with hS
    set O := oTwoRes (((Gp ⊓ M₁).subgroupOf M₁).map (f1 (c := β)) ⊔
      ((Gp ⊓ M₂).subgroupOf M₂).map (f2 (c := β))) with hO
    have hSB : S ≤ M₁ ⊓ M₂ := by
      rintro _ ⟨y, -, rfl⟩
      exact y.2.2
    have hinj := burnsideF429_bmap_injective β hβ
    have hle : ((S ⊓ oTwoRes Gp).subgroupOf (M₁ ⊓ M₂)).map (bmap β) ≤ Sp 2 Gp β ⊓ O := by
      refine le_inf ?_ h1
      rw [burnsideF429_Sp_eq]
      exact Subgroup.map_mono fun x hx => (inf_le_left : S ⊓ oTwoRes Gp ≤ S) hx
    have hidx : (((S ⊓ oTwoRes Gp).subgroupOf (M₁ ⊓ M₂)).map (bmap β)).relIndex (Sp 2 Gp β) =
        (S ⊓ oTwoRes Gp).relIndex S := by
      rw [burnsideF429_Sp_eq, Subgroup.relIndex_map_map_of_injective _ _ hinj,
        Subgroup.relIndex_subgroupOf hSB]
    have hd : (Sp 2 Gp β ⊓ O).relIndex (Sp 2 Gp β) ∣ 2 := by
      refine (Subgroup.relIndex_dvd_of_le_left (Sp 2 Gp β) hle).trans ?_
      rw [hidx]
      exact hdvd
    rcases (Nat.dvd_prime Nat.prime_two).1 hd with h | h
    · left
      exact (Subgroup.relIndex_eq_one.1 h).trans inf_le_right
    · exact Or.inr ⟨hf, hκ, h⟩

theorem burnsideF429_c8_le_of_le_perfectCore [Finite E]
    (h : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ perfectCore (Gp ⊓ M₁) ∨
      pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ perfectCore (Gp ⊓ M₂)) :
    pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤
      ((M₁ ⊓ M₂) ⊓ oTwoRes (Gp ⊓ M₁)) ⊔ ((M₁ ⊓ M₂) ⊓ oTwoRes (Gp ⊓ M₂)) := by
  have hSB : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ M₁ ⊓ M₂ := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2.2
  rcases h with h | h
  · exact le_sup_of_le_left (le_inf hSB (h.trans (burnsideF429_perfectCore_le_oTwoRes _)))
  · exact le_sup_of_le_right (le_inf hSB (h.trans (burnsideF429_perfectCore_le_oTwoRes _)))

theorem burnsideF429_c8_of_le_perfectCore [Finite E] {κ : GLKind} {f : ℕ}
    (h : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ perfectCore (Gp ⊓ M₁) ∨
      pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ perfectCore (Gp ⊓ M₂)) :
    ∀ (Y : Type) [Group Y] (β : Cpl M₁ M₂ Y), β.IsFaithful →
      ((pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ⊓ oTwoRes Gp).subgroupOf (M₁ ⊓ M₂)).map (bmap β) ≤
          oTwoRes (((Gp ⊓ M₁).subgroupOf M₁).map (f1 (c := β)) ⊔
            ((Gp ⊓ M₂).subgroupOf M₂).map (f2 (c := β))) ∧
        (Sp 2 Gp β ≤ oTwoRes (((Gp ⊓ M₁).subgroupOf M₁).map (f1 (c := β)) ⊔
              ((Gp ⊓ M₂).subgroupOf M₂).map (f2 (c := β))) ∨
          (f = 1 ∧ (κ = .Sp4 ∨ κ = .G2 ∨ κ = .F4tw) ∧
            (Sp 2 Gp β ⊓ oTwoRes (((Gp ⊓ M₁).subgroupOf M₁).map (f1 (c := β)) ⊔
              ((Gp ⊓ M₂).subgroupOf M₂).map (f2 (c := β)))).relIndex (Sp 2 Gp β) = 2)) := by
  have hb := burnsideF429_c8_le_of_le_perfectCore h
  exact burnsideF429_c8_of (κ := κ) (f := f) (inf_le_left.trans hb) (Or.inl hb)

end Clause

end CFSG.ASVolI
