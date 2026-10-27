module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP5LiftO

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open

open scoped commutatorElement

section TwFrame

variable {X Y : Type} [Group X] [Group Y] {G₀ B : Subgroup X} (fr : GGTCUFrameO G₀ B Y)

theorem GGTCUFrameO.JimgO_mono {J L : Subgroup X} (hJL : J ≤ L) : fr.JimgO J ≤ fr.JimgO L := by
  rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
  exact ⟨_, ⟨j, hJL hj, rfl⟩, rfl⟩

theorem GGTCUFrameO.ν_mem_DimgO {D : Subgroup X} (hDB : D ≤ B) {x : X} (hx : x ∈ D) :
    fr.ν ⟨x, hDB hx⟩ ∈ fr.DimgO D :=
  ⟨⟨x, hDB hx⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩

theorem GGTCUFrameO.DimgO_zpowers_le {x : X} (hx : x ∈ B) :
    fr.DimgO (Subgroup.zpowers x) ≤ Subgroup.zpowers (fr.ν ⟨x, hx⟩) := by
  rintro _ ⟨b, hb, rfl⟩
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (Subgroup.mem_subgroupOf.1 hb)
  refine Subgroup.mem_zpowers_iff.2 ⟨n, ?_⟩
  have hb' : b = ⟨x, hx⟩ ^ n := Subtype.ext (by simpa using hn.symm)
  rw [hb', map_zpow]

private theorem w5T_centralizer_zpowers_eq_single {G : Type*} [Group G] (y : G) :
    Subgroup.centralizer ((Subgroup.zpowers y : Subgroup G) : Set G) =
      Subgroup.centralizer ({y} : Set G) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

theorem GGTCUFrameO.centralizer_DimgO_zpowers {x : X} (hx : x ∈ B) :
    Subgroup.centralizer ((fr.DimgO (Subgroup.zpowers x) : Subgroup Y) : Set Y) =
      Subgroup.centralizer {fr.ν ⟨x, hx⟩} := by
  have hDB : Subgroup.zpowers x ≤ B := Subgroup.zpowers_le.2 hx
  have h1 : fr.ν ⟨x, hx⟩ ∈ fr.DimgO (Subgroup.zpowers x) :=
    fr.ν_mem_DimgO hDB (Subgroup.mem_zpowers x)
  apply le_antisymm
  · exact Subgroup.centralizer_le (Set.singleton_subset_iff.2 h1)
  · calc Subgroup.centralizer {fr.ν ⟨x, hx⟩}
        = Subgroup.centralizer ((Subgroup.zpowers (fr.ν ⟨x, hx⟩) : Subgroup Y) : Set Y) :=
          (w5T_centralizer_zpowers_eq_single _).symm
      _ ≤ _ := Subgroup.centralizer_le (SetLike.coe_subset_coe.2 (fr.DimgO_zpowers_le hx))

private theorem w5T_commutator_mem_center
    (hBN : B ≤ Subgroup.normalizer (G₀ : Set X))
    {D : Subgroup X} (hD : D ≤ B) {L : Subgroup X} (hLG : L ≤ G₀)
    (hcomm : fr.JimgO L ≤ Subgroup.centralizer ((fr.DimgO D : Subgroup Y) : Set Y)) :
    ∀ d ∈ D, ∀ k ∈ L, d * k * d⁻¹ * k⁻¹ ∈ (Subgroup.center ↥G₀).map G₀.subtype := by
  intro d hd k hk
  set b : ↥B := ⟨d, hD hd⟩ with hb
  set kG : ↥G₀ := ⟨k, hLG hk⟩ with hkG
  have hKmem : fr.Θ (QuotientGroup.mk kG) ∈ fr.JimgO L :=
    ⟨_, ⟨kG, Subgroup.mem_subgroupOf.2 hk, rfl⟩, rfl⟩
  have hDmem : fr.ν b ∈ fr.DimgO D :=
    ⟨b, Subgroup.mem_subgroupOf.2 hd, rfl⟩
  have hcen := Subgroup.mem_centralizer_iff.1 (hcomm hKmem) (fr.ν b) hDmem
  set dk : ↥G₀ := ⟨d * k * d⁻¹, GGTCUFrameO.mem_conj_of_normalizer hBN b kG⟩ with hdk
  have hact := fr.act b kG dk rfl
  have hΘ : fr.Θ (QuotientGroup.mk dk) = fr.Θ (QuotientGroup.mk kG) := by
    rw [hact, hcen, mul_inv_cancel_right]
  have hmk : (QuotientGroup.mk dk : ↥G₀ ⧸ Subgroup.center ↥G₀) =
      QuotientGroup.mk kG := fr.Θinj hΘ
  have hc : kG⁻¹ * dk ∈ Subgroup.center ↥G₀ := QuotientGroup.eq.1 hmk.symm
  refine ⟨kG⁻¹ * dk, hc, ?_⟩
  have h1 : d * k * d⁻¹ = k * ((kG⁻¹ * dk : ↥G₀) : X) := by
    simp [dk, kG, Subgroup.coe_mul]
  have h2 : ((kG⁻¹ * dk : ↥G₀) : X) * k = k * ((kG⁻¹ * dk : ↥G₀) : X) :=
    congrArg Subtype.val (Subgroup.mem_center_iff.1 hc kG).symm
  show ((kG⁻¹ * dk : ↥G₀) : X) = d * k * d⁻¹ * k⁻¹
  rw [h1, ← h2]
  group

theorem GGTCUFrameO.le_centralizer_of_langO_commute
    (hBN : B ≤ Subgroup.normalizer (G₀ : Set X)) {D L : Subgroup X} (hDB : D ≤ B)
    (hLG : L ≤ G₀) (hL : commutator ↥L = ⊤)
    (hcomm : fr.JimgO L ≤ Subgroup.centralizer ((fr.DimgO D : Subgroup Y) : Set Y)) :
    D ≤ Subgroup.centralizer (L : Set X) := by
  have hZ := w5T_commutator_mem_center fr hBN hDB hLG hcomm
  have hZJ : ∀ z ∈ (Subgroup.center ↥G₀).map G₀.subtype, ∀ j ∈ L, z * j = j * z := by
    rintro _ ⟨c, hc, rfl⟩ j hj
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.1 hc ⟨j, hLG hj⟩)).symm
  have hZZ : ∀ z ∈ (Subgroup.center ↥G₀).map G₀.subtype,
      ∀ z' ∈ (Subgroup.center ↥G₀).map G₀.subtype, z * z' = z' * z := by
    rintro _ ⟨c, hc, rfl⟩ _ ⟨c', hc', rfl⟩
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.1 hc c')).symm
  intro d hd
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  exact (commute_of_central_commutator' hL hZJ hZZ (hZ d hd) l hl).symm

private theorem w5T_perfect_le_of_le_sup_center {G : Type*} [Group G] {P Q : Subgroup G}
    (hP : ⁅P, P⁆ = P) (h : P ≤ Q ⊔ Subgroup.center G) : P ≤ Q := by
  rw [← hP, Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 (h hg₁)
  obtain ⟨y', hy', z', hz', rfl⟩ := Subgroup.mem_sup_of_normal_right.1 (h hg₂)
  have hzc : ∀ a : G, a * z = z * a := fun a => Subgroup.mem_center_iff.1 hz a
  have hzc' : ∀ a : G, a * z' = z' * a := fun a => Subgroup.mem_center_iff.1 hz' a
  have e : ⁅y * z, y' * z'⁆ = ⁅y, y'⁆ := by
    rw [commutatorElement_def, commutatorElement_def]
    calc y * z * (y' * z') * (y * z)⁻¹ * (y' * z')⁻¹
        = y * (z * (y' * z')) * z⁻¹ * y⁻¹ * (z'⁻¹ * y'⁻¹) := by group
      _ = y * ((y' * z') * z) * z⁻¹ * y⁻¹ * (z'⁻¹ * y'⁻¹) := by rw [← hzc (y' * z')]
      _ = y * (y' * z') * y⁻¹ * (z'⁻¹ * y'⁻¹) := by group
      _ = y * y' * (z' * y⁻¹) * (z'⁻¹ * y'⁻¹) := by group
      _ = y * y' * (y⁻¹ * z') * (z'⁻¹ * y'⁻¹) := by rw [← hzc' y⁻¹]
      _ = y * y' * y⁻¹ * y'⁻¹ := by group
  rw [e, commutatorElement_def]
  exact Q.mul_mem (Q.mul_mem (Q.mul_mem hy hy') (Q.inv_mem hy)) (Q.inv_mem hy')

theorem GGTCUFrameO.le_of_JimgO_le {J K : Subgroup X} (hJG : J ≤ G₀)
    (hJperf : commutator ↥J = ⊤) (h : fr.JimgO J ≤ fr.JimgO K) : J ≤ K := by
  have hperfJ : Group.IsPerfect ↥J := Group.isPerfect_def.mpr hJperf
  set J₀ : Subgroup ↥G₀ := J.subgroupOf G₀
  set K₀ : Subgroup ↥G₀ := K.subgroupOf G₀
  have hperf0 : Group.IsPerfect ↥J₀ :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hJG).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hJG).symm.surjective
  have hJ₀perf := Subgroup.isPerfect_iff.mp hperf0
  have hle : J₀ ≤ K₀ ⊔ Subgroup.center ↥G₀ := by
    intro j hj
    have hjL : fr.Θ (QuotientGroup.mk j) ∈ fr.JimgO J := ⟨_, ⟨j, hj, rfl⟩, rfl⟩
    obtain ⟨_, ⟨k₀, hk₀, rfl⟩, hq⟩ := h hjL
    have hq' : fr.langHom k₀ = fr.langHom j := hq
    have hc : k₀⁻¹ * j ∈ Subgroup.center ↥G₀ := by
      refine fr.langHom_ker _ ?_
      rw [map_mul, map_inv, hq', inv_mul_cancel]
    exact Subgroup.mem_sup_of_normal_right.2 ⟨k₀, hk₀, k₀⁻¹ * j, hc, by simp⟩
  have hJK := w5T_perfect_le_of_le_sup_center hJ₀perf hle
  intro x hx
  have hxG : (⟨x, hJG hx⟩ : ↥G₀) ∈ J₀ := Subgroup.mem_subgroupOf.2 hx
  exact Subgroup.mem_subgroupOf.1 (hJK hxG)

end TwFrame

end CFSG.StandardType.TableCRes

end
