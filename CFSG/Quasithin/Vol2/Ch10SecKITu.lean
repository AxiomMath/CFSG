module

public import CFSG.Quasithin.Vol2.Ch10SecKITa
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7
public import CFSG.Quasithin.Vol2.Ch11SecA11Cases2

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.QuasithinUnique.Vol2Native.A312L.Seven


theorem eq_rng5 (hq : CFSG.IsQuasisimple ↥A7s) {B : Subgroup ↥A7s} (hB : B ∈ lFamily T7)
    (h5 : IsAlt 5 ↥B) : B = rng5 := by
  have hB' : B ∈ cComp (B ⊔ T7) := hB
  have hc60 : Nat.card ↥B = 60 := by
    rw [Ch11.SecA.card_alt5 h5]; norm_num
  have hBtop : B ≠ ⊤ := by
    intro h
    rw [h, Subgroup.card_top, card_A7s] at hc60
    omega
  have hMne : B ⊔ T7 ≠ ⊤ := by
    intro htop
    rw [htop] at hB'
    exact hBtop (A321.cComp_eq_top_of_quasisimple hq hB')
  have hMns : ¬ Group.IsSolvable ↥(B ⊔ T7) := fun hs =>
    not_isSolvable_of_mem_cComp hB'
      (Group.isSolvable_of_isSolvable_injective
        (f := Subgroup.inclusion (le_of_mem_cComp hB' : B ≤ B ⊔ T7))
        (Subgroup.inclusion_injective _))
  obtain ⟨i, hi, hMi⟩ := overgroup_Z (le_sup_right : T7 ≤ B ⊔ T7)
  have hcardM : Nat.card ↥(B ⊔ T7) =
      [8, 24, 24, 24, 24, 24, 72, 120, 168, 168, 360, 2520].getD i 0 := by
    rw [← card_map_subtype, hMi]
    exact card_Z hi
  have hperfM : ∀ {S : Type} [Group S] [IsSimpleGroup S], (∃ a b : S, a * b ≠ b * a) →
      ↥(B ⊔ T7) ≃* S → Nat.card ↥B = Nat.card S := by
    intro S _ _ hS eM
    have hperf : ⁅B ⊔ T7, B ⊔ T7⁆ = B ⊔ T7 := perfect_of_equiv_simple hS eM
    have hpc : perfectCore (B ⊔ T7) = B ⊔ T7 := perfectCore_eq_self_of_perfect hperf
    obtain ⟨eB⟩ := lFamily_equiv_of_perfectCore_equiv hB hS
      ((MulEquiv.subgroupCongr hpc).trans eM)
    exact Nat.card_congr eB.toEquiv
  interval_cases i
  · exact absurd (isSolvable_of_card_two_three (a := 3) (b := 0) (by rw [hcardM]; decide)) hMns
  · exact absurd (isSolvable_of_card_two_three (a := 3) (b := 1) (by rw [hcardM]; decide)) hMns
  · exact absurd (isSolvable_of_card_two_three (a := 3) (b := 1) (by rw [hcardM]; decide)) hMns
  · exact absurd (isSolvable_of_card_two_three (a := 3) (b := 1) (by rw [hcardM]; decide)) hMns
  · exact absurd (isSolvable_of_card_two_three (a := 3) (b := 1) (by rw [hcardM]; decide)) hMns
  · exact absurd (isSolvable_of_card_two_three (a := 3) (b := 1) (by rw [hcardM]; decide)) hMns
  · exact absurd (isSolvable_of_card_two_three (a := 3) (b := 2) (by rw [hcardM]; decide)) hMns
  ·
    have := alt5_simple
    have hle : rng5 ≤ B ⊔ T7 := by
      intro k hk
      obtain ⟨h4, h5⟩ := (mem_rng5 k).mp hk
      exact (mem_of_map_eq hMi k).mpr
        ((mem_Z7 (Equiv.Perm.mem_alternatingGroup.mp k.2)).mpr ⟨Or.inl h4, Or.inr h5⟩)
    have hperf5 : ⁅rng5, rng5⁆ = rng5 := perfect_of_equiv_simple alt5_nonabelian rng5Equiv
    have hpc : perfectCore (B ⊔ T7) = rng5 :=
      le_antisymm ((perfectCore_le_commutator (B ⊔ T7)).trans (commutator_le_rng5 hMi))
        (le_perfectCore_of_perfect hle hperf5)
    have e : ↥(perfectCore (B ⊔ T7)) ≃* alternatingGroup (Fin 5) :=
      (MulEquiv.subgroupCongr hpc).trans rng5Equiv
    rw [← hpc]
    exact lFamily_eq_perfectCore hB alt5_nonabelian e.toMonoidHom e.surjective (by
      have hk : e.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).mpr e.injective
      rw [hk]
      infer_instance)
  ·
    have := slThree_isSimple
    have h1 := hperfM slThree_nonabelian
      (((B ⊔ T7).equivMapOfInjective A7s.subtype A7s.subtype_injective).trans
        ((MulEquiv.subgroupCongr hMi).trans z8Equiv.symm))
    rw [Matrix.card_SL_field] at h1
    simp [Fin.prod_univ_three, ZMod.card] at h1
    omega
  · have := slThree_isSimple
    have h1 := hperfM slThree_nonabelian
      (((B ⊔ T7).equivMapOfInjective A7s.subtype A7s.subtype_injective).trans
        ((MulEquiv.subgroupCongr hMi).trans z9Equiv.symm))
    rw [Matrix.card_SL_field] at h1
    simp [Fin.prod_univ_three, ZMod.card] at h1
    omega
  ·
    have := alt6_simple
    have h1 := hperfM alt6_nonabelian ((MulEquiv.subgroupCongr (eq_rng6 hMi)).trans rng6Equiv)
    rw [Ch11.SecA.card_alt6 (Y := alternatingGroup (Fin 6)) ⟨MulEquiv.refl _⟩, hc60] at h1
    exact absurd h1 (by decide)
  · exfalso
    apply hMne
    apply Subgroup.eq_top_of_card_eq
    rw [hcardM, card_A7s]
    decide

theorem a7s_quasisimple : CFSG.IsQuasisimple ↥A7s := by
  have : IsSimpleGroup ↥A7s := alternatingGroup.isSimpleGroup (by simp)
  have ha : (Equiv.swap (0 : Fin 7) 1 * Equiv.swap 1 2) ∈ A7s :=
    Equiv.Perm.mem_alternatingGroup.mpr (by decide)
  have hb : (Equiv.swap (1 : Fin 7) 2 * Equiv.swap 2 3) ∈ A7s :=
    Equiv.Perm.mem_alternatingGroup.mpr (by decide)
  have hne : (Equiv.swap (0 : Fin 7) 1 * Equiv.swap 1 2) * (Equiv.swap 1 2 * Equiv.swap 2 3) ≠
      (Equiv.swap 1 2 * Equiv.swap 2 3) * (Equiv.swap (0 : Fin 7) 1 * Equiv.swap 1 2) := by
    decide
  exact (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup
    ⟨⟨_, ha⟩, ⟨_, hb⟩, fun h => hne (congrArg Subtype.val h)⟩).1

theorem kgA7OneA5_alt {Y : Type} [Group Y] [Finite Y] (hY : IsAlt 7 Y) {T : Subgroup Y}
    (hT : IsSylowTwoOf T ⊤) {B₁ B₂ : Subgroup Y} (hB₁ : B₁ ∈ lFamily T)
    (hB₂ : B₂ ∈ lFamily T) (h₁ : IsAlt 5 ↥B₁) (h₂ : IsAlt 5 ↥B₂) : B₁ = B₂ := by
  obtain ⟨e₀⟩ := hY
  let e : Y ≃* ↥A7s := e₀
  have hT' : IsSylowTwoOf (T.map e.toMonoidHom) ⊤ :=
    A312.isSylowTwoOf_top_map e.toMonoidHom e.surjective hT
  obtain ⟨g, hg⟩ := exists_conj_of_isSylowTwoOf isSylowTwoOf_T7 hT'
  let φ : Y ≃* ↥A7s := e.trans (MulAut.conj g).symm
  have hTφ : T.map φ.toMonoidHom = T7 := by
    have : T.map φ.toMonoidHom = (T.map e.toMonoidHom).map (MulAut.conj g).symm.toMonoidHom := by
      rw [Subgroup.map_map]
      rfl
    rw [this, ← hg]
    exact map_map_symm (MulAut.conj g) T7
  have key : ∀ {B : Subgroup Y}, B ∈ lFamily T → IsAlt 5 ↥B → B.map φ.toMonoidHom = rng5 := by
    intro B hB h5
    have h1 := cComp_map_mulEquiv φ (show B ∈ cComp (B ⊔ T) from hB)
    rw [Subgroup.map_sup, hTφ] at h1
    obtain ⟨e5⟩ := h5
    exact eq_rng5 a7s_quasisimple h1
      ⟨((B.equivMapOfInjective φ.toMonoidHom φ.injective).symm).trans e5⟩
  exact Subgroup.map_injective φ.injective ((key hB₁ h₁).trans (key hB₂ h₂).symm)

theorem cComp_sup_center {Y : Type} [Group Y] [Finite Y] {B H Z : Subgroup Y}
    (hB : B ∈ cComp H) (hZ : Z ≤ Subgroup.center Y) : B ∈ cComp (H ⊔ Z) := by
  have hZc : ∀ z ∈ Z, ∀ a : Y, z * a * z⁻¹ = a := by
    intro z hz a
    have hc := Subgroup.mem_center_iff.mp (hZ hz) a
    rw [← hc, mul_inv_cancel_right]
  have hZn : ∀ z ∈ Z, ∀ A : Subgroup Y, z ∈ Subgroup.normalizer (A : Set Y) := by
    intro z hz A
    rw [Subgroup.mem_normalizer_iff]
    intro a
    rw [hZc z hz a]
  have hZnormal : Z.Normal := ⟨fun z hz g => by
    have hc := Subgroup.mem_center_iff.mp (hZ hz) g
    rw [hc, mul_inv_cancel_right]
    exact hz⟩
  have hZN : ∀ m : Y, m ∈ Subgroup.normalizer (Z : Set Y) := by
    intro m
    rw [Subgroup.mem_normalizer_iff]
    intro z
    refine ⟨fun hz => hZnormal.conj_mem z hz m, fun hz => ?_⟩
    have := hZnormal.conj_mem _ hz m⁻¹
    simpa [mul_assoc] using this
  have key : ∀ {A K : Subgroup Y}, IsSubnormal A K → IsSubnormal (A ⊔ Z) (K ⊔ Z) := by
    intro A K h
    induction h with
    | refl => exact IsSubnormal.refl _
    | @step A M K hAM hAn hMK ih =>
      refine IsSubnormal.step (sup_le_sup_right hAM Z) ?_ ih
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer (sup_le_sup_right hAM Z)]
      refine sup_le (fun m hm => ?_) (fun z hz => hZn z hz _)
      have h1 := (Subgroup.normal_subgroupOf_iff_le_normalizer hAM).mp hAn hm
      have h2 := hZN m
      rw [Subgroup.mem_normalizer_iff_map_conj_eq] at h1 h2 ⊢
      rw [Subgroup.map_sup, h1, h2]
  have hBZ : IsSubnormal B (B ⊔ Z) := A3.subnormal_of_normal le_sup_left
    ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer (fun z hz => hZn z hz B)))
  refine ⟨hB.1, hB.2.1, A3.subnormal_trans hBZ (key (subnormal_of_mem_cComp hB)), ?_⟩
  intro K hKB hK1 hKp hKs
  exact hB.2.2.2 K hKB hK1 hKp
    (A3.subnormal_of_le_of_le hKs (hKB.le.trans (le_of_mem_cComp hB)) le_sup_left)

theorem center_alt5 : Subgroup.center (alternatingGroup (Fin 5)) = ⊥ := by
  have := alt5_simple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (alternatingGroup (Fin 5)))
    with hb | ht
  · exact hb
  · exfalso
    obtain ⟨a, b, hab⟩ := alt5_nonabelian
    exact hab (Subgroup.mem_center_iff.mp (ht ▸ Subgroup.mem_top b) a)

theorem kgA7OneA5_hat {Y : Type} [Group Y] [Finite Y]
    (hY : IsHat Y ↥(alternatingGroup (Fin 7))) {T : Subgroup Y} (hT : IsSylowTwoOf T ⊤)
    {B₁ B₂ : Subgroup Y} (hB₁ : B₁ ∈ lFamily T) (hB₂ : B₂ ∈ lFamily T) (h₁ : IsAlt 5 ↥B₁)
    (h₂ : IsAlt 5 ↥B₂) : B₁ = B₂ := by
  obtain ⟨-, -, ⟨e⟩⟩ := hY
  set Z := Subgroup.center Y with hZdef
  set π := QuotientGroup.mk' Z with hπ
  have hker : π.ker = Z := QuotientGroup.ker_mk' Z
  have hπZ : Z.map π = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, hker]
  have him : ∀ {B : Subgroup Y}, B ∈ lFamily T → B.map π ∈ lFamily (T.map π) := by
    intro B hB
    have h1 := cComp_sup_center (show B ∈ cComp (B ⊔ T) from hB) (le_refl Z)
    have hks : Group.IsSolvable ↥π.ker := by
      rw [hker]
      infer_instance
    have hkle : π.ker ≤ (B ⊔ T) ⊔ Z := by
      rw [hker]
      exact le_sup_right
    have h2 := map_mem_cComp_of_le π hks hkle h1
    rw [Subgroup.map_sup, Subgroup.map_sup, hπZ, sup_bot_eq] at h2
    exact h2
  have hiso : ∀ {B : Subgroup Y}, IsAlt 5 ↥B → IsAlt 5 ↥(B.map π) := by
    intro B h5
    obtain ⟨e5⟩ := h5
    have hinj : Function.Injective (π.comp B.subtype) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro b hb
      have hbZ : (b : Y) ∈ Z := by
        rw [← hker]
        exact hb
      have hc : e5 b ∈ Subgroup.center (alternatingGroup (Fin 5)) := by
        rw [Subgroup.mem_center_iff]
        intro y
        obtain ⟨x, rfl⟩ := e5.surjective y
        rw [← map_mul, ← map_mul]
        congr 1
        apply Subtype.ext
        exact Subgroup.mem_center_iff.mp hbZ x
      rw [center_alt5, Subgroup.mem_bot, map_eq_one_iff _ e5.injective] at hc
      rw [hc]
      exact Subgroup.one_mem _
    have hrange : (π.comp B.subtype).range = B.map π := by
      ext y
      constructor
      · rintro ⟨b, rfl⟩
        exact ⟨b, b.2, rfl⟩
      · rintro ⟨b, hb, rfl⟩
        exact ⟨⟨b, hb⟩, rfl⟩
    exact ⟨((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).symm.trans e5⟩
  have hT' : IsSylowTwoOf (T.map π) ⊤ :=
    A312.isSylowTwoOf_top_map π (QuotientGroup.mk'_surjective Z) hT
  have hEq := kgA7OneA5_alt ⟨e⟩ hT' (him hB₁) (him hB₂) (hiso h₁) (hiso h₂)
  have hcore : ∀ {B : Subgroup Y}, B ∈ lFamily T → perfectCore (B ⊔ Z) = B := by
    intro B hB
    have hBp := perfect_of_mem_cComp (show B ∈ cComp (B ⊔ T) from hB)
    refine le_antisymm (perfectCore_le_of_sup_solvable le_sup_left ?_ rfl inferInstance)
      (le_perfectCore_of_perfect le_sup_left hBp)
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left]
    refine sup_le Subgroup.le_normalizer (fun z hz => ?_)
    rw [Subgroup.mem_normalizer_iff]
    intro a
    have hc := Subgroup.mem_center_iff.mp hz a
    rw [show z * a * z⁻¹ = a by rw [← hc, mul_inv_cancel_right]]
  have hsup : ∀ B : Subgroup Y, (B.map π).comap π = B ⊔ Z := by
    intro B
    rw [Subgroup.comap_map_eq, hker]
  rw [← hcore hB₁, ← hcore hB₂, ← hsup, ← hsup, hEq]

theorem kgA7OneA5_holds : KGA7OneA5 := by
  intro Y _ _ hY T hT B₁ hB₁ B₂ hB₂ h₁ h₂
  rcases hY with hY | hY
  · exact kgA7OneA5_alt hY hT hB₁ hB₂ h₁ h₂
  · exact kgA7OneA5_hat hY hT hB₁ hB₂ h₁ h₂

end CFSG.Quasithin.Vol2.Ch10.SecB.C10KH
