module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3AENineFix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenAEOrbit
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCfg9

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

theorem s16t_stab_of_mem_aSet_three {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {X : Subgroup (MulAut W)} {J : Subgroup W}
    (hind : sSupIndep (conjSubs X J)) (hne : ∀ I ∈ conjSubs X J, I ≠ ⊥)
    {A : Subgroup (MulAut W)} (hA : A ∈ E3.aSet 3 X) :
    ∀ a ∈ A, ∀ I ∈ conjSubs X J, I.map a.toMonoidHom = I := by
  by_contra hcon
  have hmove : ∃ a ∈ A, ∃ i : ↥(conjSubs X J),
      (i : Subgroup W).map a.toMonoidHom ≠ (i : Subgroup W) := by
    by_contra h
    apply hcon
    intro a ha I hI
    by_contra hne'
    exact h ⟨a, ha, ⟨I, hI⟩, hne'⟩
  have hperm : ∀ a ∈ A, ∀ i : ↥(conjSubs X J), ∃ j : ↥(conjSubs X J),
      (i : Subgroup W).map a.toMonoidHom = (j : Subgroup W) := by
    intro a ha i
    obtain ⟨g, hg, hi⟩ := i.2
    refine ⟨⟨J.map (a * g).toMonoidHom, a * g, X.mul_mem (hA.1 ha) hg, rfl⟩, ?_⟩
    have hag : (a * g).toMonoidHom = a.toMonoidHom.comp g.toMonoidHom := rfl
    show (i : Subgroup W).map a.toMonoidHom = J.map (a * g).toMonoidHom
    rw [hi, Subgroup.map_map, hag]
  obtain ⟨B, hBA, hq, hfix⟩ := s16ae_exists_index_two_fix_ne_of_moved hW
    (ι := ↥(conjSubs X J)) (Y := fun i => (i : Subgroup W)) ((sSupIndep_iff _).1 hind)
    (fun i => hne i.1 i.2) hA.2.2.1 hperm hmove
  exact hfix (hA.2.2.2 B hBA (by omega))

theorem s16t_frame_conj {W : Type} [CommGroup W] {X L Z : Subgroup (MulAut W)} {J : Subgroup W}
    (hZnorm : ∀ x ∈ X, Z.map (MulAut.conj x).toMonoidHom = Z)
    (hZL : ∀ z ∈ Z, ∀ l ∈ L, z * l = l * z) (hZJ : ∀ z ∈ Z, ∀ w ∈ J, z w ∈ J)
    (hZf : ∀ z ∈ Z, z ≠ 1 → ∃ w ∈ J, z w ≠ w) {φ : MulAut W} (hφ : φ ∈ X) :
    (∀ z ∈ Z, ∀ l ∈ L.map (MulAut.conj φ).toMonoidHom, z * l = l * z) ∧
      (∀ z ∈ Z, ∀ w ∈ J.map φ.toMonoidHom, z w ∈ J.map φ.toMonoidHom) ∧
      (∀ z ∈ Z, z ≠ 1 → ∃ w ∈ J.map φ.toMonoidHom, z w ≠ w) := by
  have hz' : ∀ z ∈ Z, MulAut.conj φ⁻¹ z ∈ Z := by
    intro z hz
    have h := hZnorm φ⁻¹ (X.inv_mem hφ)
    rw [← h]
    exact Subgroup.mem_map_of_mem _ hz
  refine ⟨?_, ?_, ?_⟩
  · intro z hz l hl
    obtain ⟨l₀, hl₀, rfl⟩ := Subgroup.mem_map.1 hl
    have hcomm := hZL (MulAut.conj φ⁻¹ z) (hz' z hz) l₀ hl₀
    show z * (φ * l₀ * φ⁻¹) = (φ * l₀ * φ⁻¹) * z
    calc z * (φ * l₀ * φ⁻¹) = φ * ((MulAut.conj φ⁻¹) z * l₀) * φ⁻¹ := by
          rw [MulAut.conj_apply]; group
      _ = φ * (l₀ * (MulAut.conj φ⁻¹) z) * φ⁻¹ := by rw [hcomm]
      _ = (φ * l₀ * φ⁻¹) * z := by rw [MulAut.conj_apply]; group
  · intro z hz w hw
    obtain ⟨w₀, hw₀, rfl⟩ := Subgroup.mem_map.1 hw
    have h1 := hZJ (MulAut.conj φ⁻¹ z) (hz' z hz) w₀ hw₀
    have hφz : z ((MulEquiv.toMonoidHom φ) w₀) =
        (MulEquiv.toMonoidHom φ) (((MulAut.conj φ⁻¹) z) w₀) := by
      change z (φ w₀) = φ (((MulAut.conj φ⁻¹) z) w₀)
      rw [← MulAut.mul_apply, ← MulAut.mul_apply]
      congr 1
      rw [MulAut.conj_apply]; group
    rw [hφz]
    exact Subgroup.mem_map_of_mem _ h1
  · intro z hz hz1
    by_contra hcon
    have hfix : ∀ w ∈ J.map φ.toMonoidHom, z w = w := by
      intro w hw
      by_contra hne
      exact hcon ⟨w, hw, hne⟩
    have hz'ne : MulAut.conj φ⁻¹ z ≠ 1 := by
      intro h1
      refine hz1 ?_
      have hφz : (MulAut.conj φ) ((MulAut.conj φ⁻¹) z) = z := by
        rw [MulAut.conj_apply, MulAut.conj_apply]; group
      have h2 := congrArg (MulAut.conj φ) h1
      rw [hφz] at h2
      simpa [MulAut.conj_apply] using h2
    obtain ⟨w, hw, hne⟩ := hZf (MulAut.conj φ⁻¹ z) (hz' z hz) hz'ne
    refine hne ?_
    have hmem : φ w ∈ J.map φ.toMonoidHom := Subgroup.mem_map_of_mem _ hw
    have h1 : z (φ w) = φ w := hfix _ hmem
    have h2 : φ ((MulAut.conj φ⁻¹ z) w) = φ w := by
      rw [← MulAut.mul_apply, show φ * MulAut.conj φ⁻¹ z = z * φ by
        rw [MulAut.conj_apply]; group, MulAut.mul_apply, h1]
    exact φ.injective h2

theorem s16t_aSet_three_eq_empty_of_case9 {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {X L Z : Subgroup (MulAut W)} (hL : IsPSL 3 2 1 ↥L)
    (hsum : SumOfNat (fun H U Z => BinaryNaturalSL H U Z 3 1) L (commSub (⊤ : Subgroup W) L) ⊥ 3)
    (hcls : Set.ncard {Y : Subgroup (MulAut W) |
      ∃ φ ∈ X, Y = L.map (MulAut.conj φ).toMonoidHom} = 2)
    (horb : (conjSubs X (commSub (⊤ : Subgroup W) L)).ncard = 2)
    (hind : sSupIndep (conjSubs X (commSub (⊤ : Subgroup W) L)))
    (hsup : sSup (conjSubs X (commSub (⊤ : Subgroup W) L)) = ⊤)
    (hZ : Nat.card ↥Z = 7) (hZnorm : ∀ x ∈ X, Z.map (MulAut.conj x).toMonoidHom = Z)
    (hZL : ∀ z ∈ Z, ∀ l ∈ L, z * l = l * z)
    (hZJ : ∀ z ∈ Z, ∀ w ∈ commSub (⊤ : Subgroup W) L, z w ∈ commSub (⊤ : Subgroup W) L)
    (hZf : ∀ z ∈ Z, z ≠ 1 → ∃ w ∈ commSub (⊤ : Subgroup W) L, z w ≠ w) :
    E3.aSet 3 X = ∅ := by
  classical
  have hN : NatSum3 L (commSub (⊤ : Subgroup W) L) := s16c167_natSum3_of_sumOfNat hsum
  have habs := s16c167_cfg9_abstract hW hL hsum hcls horb hind hsup
  have hne : ∀ I ∈ conjSubs X (commSub (⊤ : Subgroup W) L), I ≠ ⊥ := by
    intro I hI h0
    have h9 := habs.1 I hI
    rw [h0, rk_bot] at h9
    omega
  rw [Set.eq_empty_iff_forall_notMem]
  intro A hA
  have hstab := s16t_stab_of_mem_aSet_three hW hind hne hA
  have hfix : ∀ I ∈ conjSubs X (commSub (⊤ : Subgroup W) L), I ≤ fixV A := by
    intro I hI
    obtain ⟨φ, hφ, rfl⟩ := hI
    have hLφ : IsPSL 3 2 1 ↥(L.map (MulAut.conj φ).toMonoidHom) := isPSL_conjAutSub φ hL
    have hJφ : NatSum3 (L.map (MulAut.conj φ).toMonoidHom)
        ((commSub (⊤ : Subgroup W) L).map φ.toMonoidHom) := s16c167_natSum3_conj hN φ
    obtain ⟨hZLφ, hZJφ, hZfφ⟩ := s16t_frame_conj hZnorm hZL hZJ hZf hφ
    have hAs : ∀ a ∈ A, ((commSub (⊤ : Subgroup W) L).map φ.toMonoidHom).map a.toMonoidHom =
        (commSub (⊤ : Subgroup W) L).map φ.toMonoidHom :=
      fun a ha => hstab a ha _ ⟨φ, hφ, rfl⟩
    have hAL : ∀ a ∈ A, (L.map (MulAut.conj φ).toMonoidHom).map (MulAut.conj a).toMonoidHom =
        L.map (MulAut.conj φ).toMonoidHom := by
      intro a ha
      refine s16c167_normalizes_of_stab hcls horb _ ⟨φ, hφ, rfl⟩ a (hA.1 ha) ?_
      rw [s16c167_commSub_top_conj φ L]
      exact hAs a ha
    obtain ⟨B, hBA, hq, hJB⟩ := s16t_natSum3_exists_fixing_subgroup hW hLφ hJφ hZ hZLφ hZJφ
      hZfφ hA.2.2.1 hAL (fun a ha => hZnorm a (hA.1 ha)) hAs
    have hBfix : fixV B = fixV A := hA.2.2.2 B hBA (by omega)
    rw [← hBfix]
    exact hJB
  have htop : ⊤ ≤ fixV A := by
    rw [← hsup]
    exact sSup_le hfix
  apply hA.2.1
  rw [eq_bot_iff]
  intro a ha
  rw [Subgroup.mem_bot]
  apply MulEquiv.ext
  intro w
  exact (mem_fixV.1 (htop (Subgroup.mem_top w))) a ha

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
