module

public import CFSG.Quasithin.Background.F9Tilde

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open CFSG.Quasithin.CosetGeom
open scoped Pointwise

variable {G : Type*} [Group G]

theorem isElemAbelian_secImg_normalizer {K E : Subgroup G}
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y * x⁻¹ * y⁻¹ ∈ K) (hsq : ∀ x ∈ E, x ^ 2 ∈ K) :
    IsElemAbelian 2 (secImg (Subgroup.normalizer (K : Set G)) K E) := by
  rw [isElemAbelian_iff]
  constructor
  · intro y₁ hy₁ y₂ hy₂
    obtain ⟨u₁, hu₁, rfl⟩ := mem_secImg.mp hy₁
    obtain ⟨u₂, hu₂, rfl⟩ := mem_secImg.mp hy₂
    exact secMk_comm_of_commutator_mem (hcomm _ hu₁ _ hu₂)
  · intro y hy
    obtain ⟨u, hu, rfl⟩ := mem_secImg.mp hy
    rw [← map_pow]
    exact secMk_eq_one_iff.mpr (hsq _ hu)

theorem secImg_le_normalizer_secImg {K E X : Subgroup G}
    (hXE : X ≤ Subgroup.normalizer (E : Set G)) :
    secImg (Subgroup.normalizer (K : Set G)) K X ≤
      Subgroup.normalizer (secImg (Subgroup.normalizer (K : Set G)) K E :
        Set (SecQuot (Subgroup.normalizer (K : Set G)) K)) := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := mem_secImg.mp hy
  exact secMk_mem_normalizer_secImg (hXE hx)

theorem secImg_inf_centralizer_secImg {K E X : Subgroup G}
    (hXK : X ≤ Subgroup.normalizer (K : Set G)) :
    secImg (Subgroup.normalizer (K : Set G)) K E ⊓
        Subgroup.centralizer (secImg (Subgroup.normalizer (K : Set G)) K X :
          Set (SecQuot (Subgroup.normalizer (K : Set G)) K)) =
      secImg (Subgroup.normalizer (K : Set G)) K (centralizerMod K E X) := by
  ext y
  constructor
  · rintro ⟨hyE, hyC⟩
    obtain ⟨u, hu, rfl⟩ := mem_secImg.mp hyE
    refine mem_secImg.mpr ⟨u, ⟨hu, u.2, fun b hb => ?_⟩, rfl⟩
    have hcomm := Subgroup.mem_centralizer_iff.mp hyC
      (secMk (Subgroup.normalizer (K : Set G)) K ⟨b, hXK hb⟩)
      (secMk_mem_secImg (x := ⟨b, hXK hb⟩) hb)
    exact commutator_mem_of_secMk_commute (x := u) (y := ⟨b, hXK hb⟩) hcomm.symm
  · intro hy
    obtain ⟨u, ⟨huE, huN, hu⟩, rfl⟩ := mem_secImg.mp hy
    refine ⟨secMk_mem_secImg huE, Subgroup.mem_centralizer_iff.mpr fun y' hy' => ?_⟩
    obtain ⟨b, hb, rfl⟩ := mem_secImg.mp hy'
    exact (secMk_comm_of_commutator_mem (x := u) (y := b) (hu b hb)).symm

namespace F9

theorem le_normalizer_commutator_of_le {X A B : Subgroup G}
    (hA : X ≤ Subgroup.normalizer (A : Set G)) (hB : X ≤ Subgroup.normalizer (B : Set G)) :
    X ≤ Subgroup.normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  intro x hx
  apply mem_normalizer_of_conjSub_eq
  rw [← conjSub_commutator, F7.conjSub_eq_of_mem_normalizer (hA hx),
    F7.conjSub_eq_of_mem_normalizer (hB hx)]

end F9

theorem tildeOf_sup_self {V₁ X : Subgroup G} (hX : X ≤ Subgroup.normalizer (V₁ : Set G)) :
    tildeOf V₁ (X ⊔ V₁) = tildeOf V₁ X := by
  refine le_antisymm ?_ (secImg_mono le_sup_left)
  intro y hy
  obtain ⟨z, hz, rfl⟩ := mem_secImg.mp hy
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right X V₁ hX
  have hz' : (z : G) ∈ (X : Set G) * (V₁ : Set G) := by rw [← hmul]; exact hz
  obtain ⟨c, hc, v, hv, hcv⟩ := hz'
  refine mem_secImg.mpr ⟨⟨c, hX hc⟩, hc, ?_⟩
  rw [secMk_eq_secMk_iff]
  show c⁻¹ * (z : G) ∈ V₁
  rw [← hcv]
  simpa using hv

theorem tildeOf_eq_bot_of_le {V₁ X : Subgroup G} (hX : X ≤ V₁) : tildeOf V₁ X = ⊥ := by
  refine eq_bot_iff.mpr fun y hy => ?_
  obtain ⟨x, hx, rfl⟩ := mem_secImg.mp hy
  rw [secMk_eq_one_iff.mpr (hX hx)]
  exact Subgroup.one_mem _

section Fin

variable [Finite G]

theorem card_autOn_secImg {K E X : Subgroup G} (hXK : X ≤ Subgroup.normalizer (K : Set G))
    (hEK : E ≤ Subgroup.normalizer (K : Set G)) (hXE : X ≤ Subgroup.normalizer (E : Set G)) :
    Nat.card (autOn (secImg (Subgroup.normalizer (K : Set G)) K X)
        (secImg (Subgroup.normalizer (K : Set G)) K E)) =
      (centralizerMod K X E).relIndex X := by
  rw [card_autOn_eq_relIndex (secImg_le_normalizer_secImg hXE),
    secImg_inf_centralizer_secImg hEK]
  refine relIndex_secImg_of_inf_le (centralizerMod_le_left _ _ _) hXK fun x hx => ?_
  refine ⟨hx.1, Subgroup.le_normalizer hx.2, fun e he => ?_⟩
  have h1 : e * x⁻¹ * e⁻¹ ∈ K :=
    (Subgroup.mem_normalizer_iff.mp (hEK he) x⁻¹).mp (K.inv_mem hx.2)
  have e' : x * e * x⁻¹ * e⁻¹ = x * (e * x⁻¹ * e⁻¹) := by group
  rw [e']
  exact K.mul_mem hx.2 h1

theorem relIndex_secImg_fix {K E X : Subgroup G} (hXK : X ≤ Subgroup.normalizer (K : Set G))
    (hEK : E ≤ Subgroup.normalizer (K : Set G)) :
    (secImg (Subgroup.normalizer (K : Set G)) K E ⊓
        Subgroup.centralizer (secImg (Subgroup.normalizer (K : Set G)) K X :
          Set (SecQuot (Subgroup.normalizer (K : Set G)) K))).relIndex
        (secImg (Subgroup.normalizer (K : Set G)) K E) =
      (centralizerMod K E X).relIndex E := by
  rw [secImg_inf_centralizer_secImg hXK]
  refine relIndex_secImg_of_inf_le (centralizerMod_le_left _ _ _) hEK fun x hx => ?_
  refine ⟨hx.1, Subgroup.le_normalizer hx.2, fun b hb => ?_⟩
  have h1 : b * x⁻¹ * b⁻¹ ∈ K :=
    (Subgroup.mem_normalizer_iff.mp (hXK hb) x⁻¹).mp (K.inv_mem hx.2)
  have e' : x * b * x⁻¹ * b⁻¹ = x * (b * x⁻¹ * b⁻¹) := by group
  rw [e']
  exact K.mul_mem hx.2 h1

theorem isFFModule_autOn_secImg {K E X' B : Subgroup G}
    (hE : IsElemAbelian 2 (secImg (Subgroup.normalizer (K : Set G)) K E))
    (hEK : E ≤ Subgroup.normalizer (K : Set G)) (hX'K : X' ≤ Subgroup.normalizer (K : Set G))
    (hX'E : X' ≤ Subgroup.normalizer (E : Set G)) (hBX' : B ≤ X') (hBel : IsElemAbelian 2 B)
    (hnt : ¬ ∀ b ∈ B, ∀ e ∈ E, b * e * b⁻¹ * e⁻¹ ∈ K)
    (hle : (centralizerMod K E B).relIndex E ≤ (centralizerMod K B E).relIndex B) :
    @IsFFModule ↥(secImg (Subgroup.normalizer (K : Set G)) K E) (commGroupOfElemAbelian hE)
      (autOn (secImg (Subgroup.normalizer (K : Set G)) K X')
        (secImg (Subgroup.normalizer (K : Set G)) K E)) := by
  let _ : CommGroup ↥(secImg (Subgroup.normalizer (K : Set G)) K E) := commGroupOfElemAbelian hE
  have hBK : B ≤ Subgroup.normalizer (K : Set G) := hBX'.trans hX'K
  have hBE : B ≤ Subgroup.normalizer (E : Set G) := hBX'.trans hX'E
  have hBt : IsElemAbelian 2 (secImg (Subgroup.normalizer (K : Set G)) K B) :=
    isElemAbelian_secImg hBel
  have hn := secImg_le_normalizer_secImg (K := K) (E := E) (X := B) hBE
  refine ⟨autOn (secImg (Subgroup.normalizer (K : Set G)) K B)
    (secImg (Subgroup.normalizer (K : Set G)) K E),
    autOn_le_autOn _ (secImg_mono hBX'), ?_, isElemAbelian2_autOn hE hBt hn, ?_⟩
  · refine autOn_ne_bot_of_not_le_centralizer hn ?_
    intro hle'
    apply hnt
    intro b hb e he
    have := Subgroup.mem_centralizer_iff.mp
      (hle' (secMk_mem_secImg (x := ⟨b, hBK hb⟩) hb))
      (secMk (Subgroup.normalizer (K : Set G)) K ⟨e, hEK he⟩)
      (secMk_mem_secImg (x := ⟨e, hEK he⟩) he)
    exact commutator_mem_of_secMk_commute (x := ⟨b, hBK hb⟩) (y := ⟨e, hEK he⟩) this.symm
  · have c1 := card_autOn_secImg hBK hEK hBE
    have c2 := card_fixV_autOn_eq hE hn
    have c3 := relIndex_secImg_fix (K := K) (E := E) (X := B) hBK hEK
    have hmul := Subgroup.relIndex_mul_card
      (secImg (Subgroup.normalizer (K : Set G)) K E ⊓ Subgroup.centralizer
        (secImg (Subgroup.normalizer (K : Set G)) K B :
          Set (SecQuot (Subgroup.normalizer (K : Set G)) K)))
      (secImg (Subgroup.normalizer (K : Set G)) K E)
    rw [inf_eq_left.mpr inf_le_left] at hmul
    rw [c1, c2]
    calc Nat.card ↥(secImg (Subgroup.normalizer (K : Set G)) K E)
        = (secImg (Subgroup.normalizer (K : Set G)) K E ⊓ Subgroup.centralizer
          (secImg (Subgroup.normalizer (K : Set G)) K B :
            Set (SecQuot (Subgroup.normalizer (K : Set G)) K))).relIndex
            (secImg (Subgroup.normalizer (K : Set G)) K E) *
          Nat.card ↥(secImg (Subgroup.normalizer (K : Set G)) K E ⊓ Subgroup.centralizer
          (secImg (Subgroup.normalizer (K : Set G)) K B :
            Set (SecQuot (Subgroup.normalizer (K : Set G)) K))) := hmul.symm
      _ ≤ (centralizerMod K B E).relIndex B *
          Nat.card ↥(secImg (Subgroup.normalizer (K : Set G)) K E ⊓ Subgroup.centralizer
          (secImg (Subgroup.normalizer (K : Set G)) K B :
            Set (SecQuot (Subgroup.normalizer (K : Set G)) K))) := by
        rw [c3]; exact Nat.mul_le_mul_right _ hle

theorem isStrongFFModule_autOn_secImg {K E X' B : Subgroup G}
    (hE : IsElemAbelian 2 (secImg (Subgroup.normalizer (K : Set G)) K E))
    (hEK : E ≤ Subgroup.normalizer (K : Set G)) (hX'K : X' ≤ Subgroup.normalizer (K : Set G))
    (hX'E : X' ≤ Subgroup.normalizer (E : Set G)) (hBX' : B ≤ X') (hBel : IsElemAbelian 2 B)
    (hnt : ¬ ∀ b ∈ B, ∀ e ∈ E, b * e * b⁻¹ * e⁻¹ ∈ K)
    (hlt : (centralizerMod K E B).relIndex E < (centralizerMod K B E).relIndex B) :
    @IsStrongFFModule ↥(secImg (Subgroup.normalizer (K : Set G)) K E) (commGroupOfElemAbelian hE)
      (autOn (secImg (Subgroup.normalizer (K : Set G)) K X')
        (secImg (Subgroup.normalizer (K : Set G)) K E)) := by
  let _ : CommGroup ↥(secImg (Subgroup.normalizer (K : Set G)) K E) := commGroupOfElemAbelian hE
  have hBK : B ≤ Subgroup.normalizer (K : Set G) := hBX'.trans hX'K
  have hBE : B ≤ Subgroup.normalizer (E : Set G) := hBX'.trans hX'E
  have hBt : IsElemAbelian 2 (secImg (Subgroup.normalizer (K : Set G)) K B) :=
    isElemAbelian_secImg hBel
  have hn := secImg_le_normalizer_secImg (K := K) (E := E) (X := B) hBE
  refine ⟨autOn (secImg (Subgroup.normalizer (K : Set G)) K B)
    (secImg (Subgroup.normalizer (K : Set G)) K E),
    autOn_le_autOn _ (secImg_mono hBX'), ?_, isElemAbelian2_autOn hE hBt hn, ?_⟩
  · refine autOn_ne_bot_of_not_le_centralizer hn ?_
    intro hle'
    apply hnt
    intro b hb e he
    have := Subgroup.mem_centralizer_iff.mp
      (hle' (secMk_mem_secImg (x := ⟨b, hBK hb⟩) hb))
      (secMk (Subgroup.normalizer (K : Set G)) K ⟨e, hEK he⟩)
      (secMk_mem_secImg (x := ⟨e, hEK he⟩) he)
    exact commutator_mem_of_secMk_commute (x := ⟨b, hBK hb⟩) (y := ⟨e, hEK he⟩) this.symm
  · have c1 := card_autOn_secImg hBK hEK hBE
    have c2 := card_fixV_autOn_eq hE hn
    have c3 := relIndex_secImg_fix (K := K) (E := E) (X := B) hBK hEK
    have hmul := Subgroup.relIndex_mul_card
      (secImg (Subgroup.normalizer (K : Set G)) K E ⊓ Subgroup.centralizer
        (secImg (Subgroup.normalizer (K : Set G)) K B :
          Set (SecQuot (Subgroup.normalizer (K : Set G)) K)))
      (secImg (Subgroup.normalizer (K : Set G)) K E)
    rw [inf_eq_left.mpr inf_le_left] at hmul
    have hpos : 0 < Nat.card ↥(secImg (Subgroup.normalizer (K : Set G)) K E ⊓
        Subgroup.centralizer (secImg (Subgroup.normalizer (K : Set G)) K B :
          Set (SecQuot (Subgroup.normalizer (K : Set G)) K))) := Nat.card_pos
    rw [c1, c2]
    calc Nat.card ↥(secImg (Subgroup.normalizer (K : Set G)) K E)
        = (secImg (Subgroup.normalizer (K : Set G)) K E ⊓ Subgroup.centralizer
          (secImg (Subgroup.normalizer (K : Set G)) K B :
            Set (SecQuot (Subgroup.normalizer (K : Set G)) K))).relIndex
            (secImg (Subgroup.normalizer (K : Set G)) K E) *
          Nat.card ↥(secImg (Subgroup.normalizer (K : Set G)) K E ⊓ Subgroup.centralizer
          (secImg (Subgroup.normalizer (K : Set G)) K B :
            Set (SecQuot (Subgroup.normalizer (K : Set G)) K))) := hmul.symm
      _ < (centralizerMod K B E).relIndex B *
          Nat.card ↥(secImg (Subgroup.normalizer (K : Set G)) K E ⊓ Subgroup.centralizer
          (secImg (Subgroup.normalizer (K : Set G)) K B :
            Set (SecQuot (Subgroup.normalizer (K : Set G)) K))) := by
        rw [c3]; exact Nat.mul_lt_mul_of_pos_right hlt hpos

theorem mem_Qset_autOn_secImg {K E X' B : Subgroup G}
    (hE : IsElemAbelian 2 (secImg (Subgroup.normalizer (K : Set G)) K E))
    (hEK : E ≤ Subgroup.normalizer (K : Set G)) (hX'K : X' ≤ Subgroup.normalizer (K : Set G))
    (hX'E : X' ≤ Subgroup.normalizer (E : Set G)) (hBX' : B ≤ X') (hBel : IsElemAbelian 2 B)
    (hnt : ¬ ∀ b ∈ B, ∀ e ∈ E, b * e * b⁻¹ * e⁻¹ ∈ K)
    (hquad : ∀ b₁ ∈ B, ∀ b₂ ∈ B, ∀ e ∈ E,
      b₂ * (b₁ * e * b₁⁻¹ * e⁻¹) * b₂⁻¹ * (b₁ * e * b₁⁻¹ * e⁻¹)⁻¹ ∈ K)
    (hr : (centralizerMod K E B).relIndex E ≤ ((centralizerMod K B E).relIndex B) ^ 2) :
    autOn (secImg (Subgroup.normalizer (K : Set G)) K B)
        (secImg (Subgroup.normalizer (K : Set G)) K E) ∈
      @Qset ↥(secImg (Subgroup.normalizer (K : Set G)) K E) (commGroupOfElemAbelian hE)
        (autOn (secImg (Subgroup.normalizer (K : Set G)) K X')
          (secImg (Subgroup.normalizer (K : Set G)) K E)) := by
  let _ : CommGroup ↥(secImg (Subgroup.normalizer (K : Set G)) K E) := commGroupOfElemAbelian hE
  have hBK : B ≤ Subgroup.normalizer (K : Set G) := hBX'.trans hX'K
  have hBE : B ≤ Subgroup.normalizer (E : Set G) := hBX'.trans hX'E
  have hBt : IsElemAbelian 2 (secImg (Subgroup.normalizer (K : Set G)) K B) :=
    isElemAbelian_secImg hBel
  have hn := secImg_le_normalizer_secImg (K := K) (E := E) (X := B) hBE
  have hA2 : IsA2 (autOn (secImg (Subgroup.normalizer (K : Set G)) K X')
      (secImg (Subgroup.normalizer (K : Set G)) K E))
      (autOn (secImg (Subgroup.normalizer (K : Set G)) K B)
        (secImg (Subgroup.normalizer (K : Set G)) K E)) := by
    refine ⟨autOn_le_autOn _ (secImg_mono hBX'), ?_, isElemAbelian2_autOn hE hBt hn⟩
    refine autOn_ne_bot_of_not_le_centralizer hn ?_
    intro hle'
    apply hnt
    intro b hb e he
    have := Subgroup.mem_centralizer_iff.mp
      (hle' (secMk_mem_secImg (x := ⟨b, hBK hb⟩) hb))
      (secMk (Subgroup.normalizer (K : Set G)) K ⟨e, hEK he⟩)
      (secMk_mem_secImg (x := ⟨e, hEK he⟩) he)
    exact commutator_mem_of_secMk_commute (x := ⟨b, hBK hb⟩) (y := ⟨e, hEK he⟩) this.symm
  refine ⟨⟨hA2, ?_⟩, ?_⟩
  · rw [rAV_le_two_iff (fun w => Subtype.ext (by simpa using hE.2 w w.2)) hA2]
    have c1 := card_autOn_secImg hBK hEK hBE
    have c2 := card_fixV_autOn_eq hE hn
    have c3 := relIndex_secImg_fix (K := K) (E := E) (X := B) hBK hEK
    have hmul := Subgroup.relIndex_mul_card
      (secImg (Subgroup.normalizer (K : Set G)) K E ⊓ Subgroup.centralizer
        (secImg (Subgroup.normalizer (K : Set G)) K B :
          Set (SecQuot (Subgroup.normalizer (K : Set G)) K)))
      (secImg (Subgroup.normalizer (K : Set G)) K E)
    rw [inf_eq_left.mpr inf_le_left] at hmul
    rw [c1, c2]
    calc Nat.card ↥(secImg (Subgroup.normalizer (K : Set G)) K E)
        = (secImg (Subgroup.normalizer (K : Set G)) K E ⊓ Subgroup.centralizer
          (secImg (Subgroup.normalizer (K : Set G)) K B :
            Set (SecQuot (Subgroup.normalizer (K : Set G)) K))).relIndex
            (secImg (Subgroup.normalizer (K : Set G)) K E) *
          Nat.card ↥(secImg (Subgroup.normalizer (K : Set G)) K E ⊓ Subgroup.centralizer
          (secImg (Subgroup.normalizer (K : Set G)) K B :
            Set (SecQuot (Subgroup.normalizer (K : Set G)) K))) := hmul.symm
      _ ≤ ((centralizerMod K B E).relIndex B) ^ 2 *
          Nat.card ↥(secImg (Subgroup.normalizer (K : Set G)) K E ⊓ Subgroup.centralizer
          (secImg (Subgroup.normalizer (K : Set G)) K B :
            Set (SecQuot (Subgroup.normalizer (K : Set G)) K))) := by
        rw [c3]; exact Nat.mul_le_mul_right _ hr
  · rw [← isQuadratic_iff_commSeries_two]
    refine isQuadratic_autOn_of_forall hE ?_
    intro s₁ hs₁ s₂ hs₂ w hw
    obtain ⟨b₁, hb₁, rfl⟩ := mem_secImg.mp hs₁
    obtain ⟨b₂, hb₂, rfl⟩ := mem_secImg.mp hs₂
    obtain ⟨u, hu, rfl⟩ := mem_secImg.mp hw
    have h1 : secMk (Subgroup.normalizer (K : Set G)) K
        (b₂ * (b₁ * u * b₁⁻¹ * u⁻¹) * b₂⁻¹ * (b₁ * u * b₁⁻¹ * u⁻¹)⁻¹) = 1 :=
      secMk_eq_one_iff.mpr (by simpa using hquad b₁ hb₁ b₂ hb₂ u hu)
    simpa [map_mul, map_inv] using h1

theorem mem_Qset_of_le {W : Type*} [CommGroup W] {X X' A : Subgroup (MulAut W)}
    (hA : A ∈ Qset X) (hAX' : A ≤ X') : A ∈ Qset X' :=
  ⟨⟨⟨hAX', hA.1.1.2⟩, hA.1.2⟩, hA.2⟩

end Fin

end CFSG.Quasithin
