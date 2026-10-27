module

public import CFSG.Timmesfeld.ARS.CaseOASurj

public section

namespace CFSG.Timmesfeld.ARS

open CFSG.Timmesfeld.RankOne CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg Matrix
  CFSG.Blueprint

variable {G : Type} [Group G] {R : Set (Subgroup G)}

theorem IsConfig.nonadj_subgroupOf {r : ℕ} {adj : Fin r → Fin r → Prop} {A B : Fin r → Subgroup G}
    (hX : IsConfig R adj A B) {L : Subgroup G} (hle : ∀ k, A k ⊔ B k ≤ L) :
    ∀ i j, i ≠ j → ¬ adj i j → ¬ adj j i →
      Commuting ((A i).subgroupOf L) ((A j).subgroupOf L) ∧
      Commuting ((A i).subgroupOf L) ((B j).subgroupOf L) ∧
      Commuting ((B i).subgroupOf L) ((A j).subgroupOf L) ∧
      Commuting ((B i).subgroupOf L) ((B j).subgroupOf L) := by
  intro i j hij h1 h2
  obtain ⟨c1, c2, c3, c4⟩ := hX.nonadj i j hij h1 h2
  have hA := fun k => le_sup_left.trans (hle k)
  have hB := fun k => le_sup_right.trans (hle k)
  exact ⟨(Sec13Restrict.commuting_subgroupOf_iff' (hA i) (hA j)).2 c1,
    (Sec13Restrict.commuting_subgroupOf_iff' (hA i) (hB j)).2 c2,
    (Sec13Restrict.commuting_subgroupOf_iff' (hB i) (hA j)).2 c3,
    (Sec13Restrict.commuting_subgroupOf_iff' (hB i) (hB j)).2 c4⟩

theorem IsConfig.exists_ne_one_subgroupOf (hR : IsRootClass R) {r : ℕ}
    {adj : Fin r → Fin r → Prop} {A B : Fin r → Subgroup G} (hX : IsConfig R adj A B)
    {L : Subgroup G} (hle : ∀ k, A k ⊔ B k ≤ L) (k : Fin r) :
    ∃ k, ∃ a ∈ (A k).subgroupOf L, a ≠ 1 := by
  obtain ⟨a, ha, ha1⟩ := hR.exists_ne_one (hX.memA k)
  refine ⟨k, ⟨a, le_sup_left.trans (hle _) ha⟩, ha, fun h => ha1 ?_⟩
  exact congrArg Subtype.val h

theorem IsConfig.exists_surjective_A_two_le [Finite G] (hR : IsRootClass R)
    (hiso : NoIsolated R) {L : Subgroup G} {A B : Fin 2 → Subgroup G}
    (hX : IsConfig R (edgeA 2) A B) (hgen : ⨆ k, (A k ⊔ B k) = L) :
    ∃ f : ℕ, 1 ≤ f ∧
      ∃ Ψ : SpecialLinearGroup (Fin (2 + 1)) (GaloisField 2 f) →* ↥L,
        (∀ k : Fin 2, ((SpecialLinear.rootDatum 2 (GaloisField 2 f)).rootGroup (sroot k)).map Ψ =
          (A k).subgroupOf L) ∧
        (∀ k : Fin 2, ((SpecialLinear.rootDatum 2 (GaloisField 2 f)).rootGroup (-sroot k)).map Ψ =
          (B k).subgroupOf L) ∧ Function.Surjective Ψ := by
  have hle : ∀ k, A k ⊔ B k ≤ L := fun k => hgen ▸ le_iSup (fun k => A k ⊔ B k) k
  obtain ⟨f, hf, ρ, hρ, hedge⟩ := hX.exists_frame_le hR hiso (isRootedTree_A (by omega)) hle
  set F := GaloisField 2 f
  obtain ⟨ψ, hψ⟩ := hedge 0 1 (by decide)
  have hu : ∀ k, Set.range (fun c => ρ k (tv 0 1 c)) = ((A k).subgroupOf L : Set ↥L) :=
    fun k => by
      rw [← (hρ k).1]
      exact Linear.range_tv_upper (ρ k)
  have hv : ∀ k, Set.range (fun c => ρ k (tv 1 0 c)) = ((B k).subgroupOf L : Set ↥L) :=
    fun k => by
      rw [← (hρ k).2]
      exact Linear.range_tv_lower (ρ k)
  have mu : ∀ k c, ρ k (tv 0 1 c) ∈ (A k).subgroupOf L := fun k c => by
    rw [← SetLike.mem_coe, ← hu]
    exact ⟨c, rfl⟩
  have mv : ∀ k c, ρ k (tv 1 0 c) ∈ (B k).subgroupOf L := fun k c => by
    rw [← SetLike.mem_coe, ← hv]
    exact ⟨c, rfl⟩
  have hxu : ∀ (k : Fin 2) (c : F), ψ (SL.x 2 F (sroot k) c) = ρ k (tv 0 1 c) := by
    intro k c
    rw [Linear.x_sroot]
    fin_cases k
    · exact (hψ c).1
    · exact (hψ c).2.2.1
  have hxv : ∀ (k : Fin 2) (c : F), ψ (SL.x 2 F (-sroot k) c) = ρ k (tv 1 0 c) := by
    intro k c
    rw [Linear.x_neg_sroot]
    fin_cases k
    · exact (hψ c).2.1
    · exact (hψ c).2.2.2
  have hD := simplyLacedLevis_specialLinear 2 F
  have hroot : ∀ k : Fin 2, sroot k ∈ (SpecialLinear.rootDatum 2 F).roots ∧
      -sroot k ∈ (SpecialLinear.rootDatum 2 F).roots := fun k =>
    ⟨(Levi.single_mem_pairRoots (D := SpecialLinear.rootDatum 2 F) (i := k) (j := k)
      (Or.inl rfl)).1.1,
      (Levi.single_mem_pairRoots (D := SpecialLinear.rootDatum 2 F) (i := k) (j := k)
        (Or.inl rfl)).2.1⟩
  have hmap : ∀ (γ : Fin 2 → ℤ) (S : Subgroup ↥L), γ ∈ (SpecialLinear.rootDatum 2 F).roots →
      (∀ c, ψ (SL.x 2 F γ c) ∈ S) → (∀ s ∈ S, ∃ c, ψ (SL.x 2 F γ c) = s) →
      ((SpecialLinear.rootDatum 2 F).rootGroup γ).map ψ = S := by
    intro γ S hγ h1 h2
    ext y
    constructor
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨c, rfl⟩ := hD.surj _ hγ g hg
      exact h1 c
    · intro hy
      obtain ⟨c, rfl⟩ := h2 y hy
      exact ⟨_, hD.mem _ hγ c, rfl⟩
  have hA : ∀ k : Fin 2, ((SpecialLinear.rootDatum 2 F).rootGroup (sroot k)).map ψ =
      (A k).subgroupOf L := by
    intro k
    refine hmap _ _ (hroot k).1 (fun c => ?_) (fun s hs => ?_)
    · exact (congrArg (· ∈ (A k).subgroupOf L) (hxu k c)).mpr (mu k c)
    · rw [← SetLike.mem_coe, ← hu k] at hs
      obtain ⟨c, rfl⟩ := hs
      exact ⟨c, hxu k c⟩
  have hB : ∀ k : Fin 2, ((SpecialLinear.rootDatum 2 F).rootGroup (-sroot k)).map ψ =
      (B k).subgroupOf L := by
    intro k
    refine hmap _ _ (hroot k).2 (fun c => ?_) (fun s hs => ?_)
    · exact (congrArg (· ∈ (B k).subgroupOf L) (hxv k c)).mpr (mv k c)
    · rw [← SetLike.mem_coe, ← hv k] at hs
      obtain ⟨c, rfl⟩ := hs
      exact ⟨c, hxv k c⟩
  refine ⟨f, hf, ψ, hA, hB, ?_⟩
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← iSup_subgroupOf_eq_top_of_iSup_eq hgen]
  refine iSup_le fun k => sup_le ?_ ?_
  · intro a ha
    rw [← SetLike.mem_coe, ← hu] at ha
    obtain ⟨c, rfl⟩ := ha
    exact ⟨_, hxu k c⟩
  · intro b hb
    rw [← SetLike.mem_coe, ← hv] at hb
    obtain ⟨c, rfl⟩ := hb
    exact ⟨_, hxv k c⟩

theorem IsConfig.exists_surjective_E6_le [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R)
    {L : Subgroup G} {A B : Fin 6 → Subgroup G} (hX : IsConfig R (edgeE 6) A B)
    (hgen : ⨆ k, (A k ⊔ B k) = L) :
    ∃ f : ℕ, 1 ≤ f ∧
      ∃ Ψ : ↥(Minuscule.e6Data_valid.minGroup (GaloisField 2 f)) →* ↥L,
        (∀ k, ((Minuscule.e6Datum (GaloisField 2 f)).rootGroup (sroot k)).map Ψ =
          (A k).subgroupOf L) ∧
        (∀ k, ((Minuscule.e6Datum (GaloisField 2 f)).rootGroup (-sroot k)).map Ψ =
          (B k).subgroupOf L) ∧ Function.Surjective Ψ := by
  have hle : ∀ k, A k ⊔ B k ≤ L := fun k => hgen ▸ le_iSup (fun k => A k ⊔ B k) k
  obtain ⟨f, hf, ρ, hρ, hedge⟩ := hX.exists_frame_le hR hiso (isRootedTree_E (by norm_num)) hle
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F := GaloisField 2 f
  obtain ⟨Ψ, hΨA, hΨB, hsurj, -⟩ := exists_surjective_of_rho (D := Minuscule.e6Datum F)
    (CurtisTits.curtisTitsConclusion_e6 2 f ⟨Nat.prime_two, hf, rfl⟩)
    (leviConePresented_e6 F) (simplyLacedLevis_e6 F) (hX.nonadj_subgroupOf hle) ρ hρ hedge
    (iSup_subgroupOf_eq_top_of_iSup_eq hgen) (hX.exists_ne_one_subgroupOf hR hle 0)
  exact ⟨f, hf, Ψ, hΨA, hΨB, hsurj⟩

theorem IsConfig.exists_surjective_E7_le [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R)
    {L : Subgroup G} {A B : Fin 7 → Subgroup G} (hX : IsConfig R (edgeE 7) A B)
    (hgen : ⨆ k, (A k ⊔ B k) = L) :
    ∃ f : ℕ, 1 ≤ f ∧
      ∃ Ψ : ↥(Minuscule.e7Data_valid.minGroup (GaloisField 2 f)) →* ↥L,
        (∀ k, ((Minuscule.e7Datum (GaloisField 2 f)).rootGroup (sroot k)).map Ψ =
          (A k).subgroupOf L) ∧
        (∀ k, ((Minuscule.e7Datum (GaloisField 2 f)).rootGroup (-sroot k)).map Ψ =
          (B k).subgroupOf L) ∧ Function.Surjective Ψ := by
  have hle : ∀ k, A k ⊔ B k ≤ L := fun k => hgen ▸ le_iSup (fun k => A k ⊔ B k) k
  obtain ⟨f, hf, ρ, hρ, hedge⟩ := hX.exists_frame_le hR hiso (isRootedTree_E (by norm_num)) hle
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F := GaloisField 2 f
  obtain ⟨Ψ, hΨA, hΨB, hsurj, -⟩ := exists_surjective_of_rho (D := Minuscule.e7Datum F)
    (CurtisTits.curtisTitsConclusion_e7 2 f ⟨Nat.prime_two, hf, rfl⟩)
    (leviConePresented_e7 F) (simplyLacedLevis_e7 F) (hX.nonadj_subgroupOf hle) ρ hρ hedge
    (iSup_subgroupOf_eq_top_of_iSup_eq hgen) (hX.exists_ne_one_subgroupOf hR hle 0)
  exact ⟨f, hf, Ψ, hΨA, hΨB, hsurj⟩

theorem IsConfig.exists_surjective_E8_le [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R)
    {L : Subgroup G} {A B : Fin 8 → Subgroup G} (hX : IsConfig R (edgeE 8) A B)
    (hgen : ⨆ k, (A k ⊔ B k) = L) :
    ∃ f : ℕ, 1 ≤ f ∧
      ∃ Ψ : ↥(Chevalley.adjointGroup .E8 (GaloisField 2 f)) →* ↥L,
        (∀ k, ((Adjoint.e8Datum (GaloisField 2 f)).rootGroup (sroot k)).map Ψ =
          (A k).subgroupOf L) ∧
        (∀ k, ((Adjoint.e8Datum (GaloisField 2 f)).rootGroup (-sroot k)).map Ψ =
          (B k).subgroupOf L) ∧ Function.Surjective Ψ := by
  have hle : ∀ k, A k ⊔ B k ≤ L := fun k => hgen ▸ le_iSup (fun k => A k ⊔ B k) k
  obtain ⟨f, hf, ρ, hρ, hedge⟩ := hX.exists_frame_le hR hiso (isRootedTree_E (by norm_num)) hle
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F := GaloisField 2 f
  obtain ⟨Ψ, hΨA, hΨB, hsurj, -⟩ := exists_surjective_of_rho (D := Adjoint.e8Datum F)
    (CurtisTits.curtisTitsConclusion_e8 2 f ⟨Nat.prime_two, hf, rfl⟩)
    (leviConePresented_e8 F) (simplyLacedLevis_e8 F) (hX.nonadj_subgroupOf hle) ρ hρ hedge
    (iSup_subgroupOf_eq_top_of_iSup_eq hgen) (hX.exists_ne_one_subgroupOf hR hle 0)
  exact ⟨f, hf, Ψ, hΨA, hΨB, hsurj⟩

end CFSG.Timmesfeld.ARS
