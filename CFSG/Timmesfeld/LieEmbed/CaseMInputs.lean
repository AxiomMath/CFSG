module

public import CFSG.Timmesfeld.ARS.CaseMLieInputs
public import CFSG.Timmesfeld.LieEmbed.SpF4
public import CFSG.Timmesfeld.LieEmbed.F4Edge
public import CFSG.Timmesfeld.LieEmbed.SUTwistedE6
public import CFSG.Timmesfeld.LieEmbed.TwistedE6Edge

public section

namespace CFSG.Timmesfeld.LieEmbed

open CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Steinberg CFSG.LieType.Universal
open CFSG.Timmesfeld.ARS.CaseM

theorem c3PairRoots_check : ∀ γ ∈ c3PairRoots, γ 0 = 0 ∧ c3Coords γ ∈ c3Roots := by
  rintro γ (hγ | ⟨δ, hδ, rfl⟩)
  · simp only [c3PosRoots, Set.mem_insert_iff, Set.mem_singleton_iff] at hγ
    rcases hγ with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · simp only [c3PosRoots, Set.mem_insert_iff, Set.mem_singleton_iff] at hδ
    rcases hδ with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem c3ToF4_c3Coords {γ : Fin 4 → ℤ} (h0 : γ 0 = 0) : c3ToF4 (c3Coords γ) = γ := by
  funext i
  fin_cases i
  · exact h0.symm
  all_goals rfl

theorem f4C3LeviInput : F4C3LeviInput := by
  intro f _
  obtain ⟨ι, hinj, hι⟩ := exists_spToF4 (K := GaloisField 2 f)
  refine ⟨ι, hinj, fun γ hγ => ?_⟩
  obtain ⟨h0, hr⟩ := c3PairRoots_check γ hγ
  have h := image_rootGroup_spToF4 hι (mem_roots_of_mem_c3Roots hr)
  rwa [c3ToF4_c3Coords h0] at h

theorem coe_f4RootGroup {K : Type} [Field K] {γ : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ)
    {u : K → ↥(adjointGroup .F4 K)} (hu : ∀ c, u c = Adjoint.f4Par K γ c) :
    ((Adjoint.f4Datum K).rootGroup γ : Set ↥(adjointGroup .F4 K)) = Set.range u := by
  ext g
  rw [SetLike.mem_coe, Adjoint.mem_rootGroup_iff hγ, Set.mem_range]
  simp only [hu]

theorem f4EdgeLeviInput : F4EdgeLeviInput := by
  intro f _
  obtain ⟨l, hinj, hl⟩ := exists_sl3ToF4 (K := GaloisField 2 f)
  have e0 : (sroot (f4n 0) : Fin (Tag.rank .F4) → ℤ) = ![1, 0, 0, 0] := by
    funext i; fin_cases i <;> rfl
  have e1 : (sroot (f4n 1) : Fin (Tag.rank .F4) → ℤ) = ![0, 1, 0, 0] := by
    funext i; fin_cases i <;> rfl
  have e01 : (sroot (f4n 0) + sroot (f4n 1) : Fin (Tag.rank .F4) → ℤ) = ![1, 1, 0, 0] := by
    funext i; fin_cases i <;> rfl
  have r01 : IsRoot .F4 (sroot (f4n 0) + sroot (f4n 1)) := mem_rootFinset.1 (by decide)
  have r01' : IsRoot .F4 (-(sroot (f4n 0) + sroot (f4n 1))) := mem_rootFinset.1 (by decide)
  rw [← e0, ← e1, ← e01]
  have r0 := isRoot_single .F4 (f4n 0)
  have r0' := isRoot_neg_single .F4 (f4n 0)
  have r1 := isRoot_single .F4 (f4n 1)
  have r1' := isRoot_neg_single .F4 (f4n 1)
  refine ⟨l, hinj, coe_f4RootGroup r0 fun c => (hl c).1,
    coe_f4RootGroup r0' fun c => (hl c).2.1, coe_f4RootGroup r1 fun c => (hl c).2.2.1,
    coe_f4RootGroup r1' fun c => (hl c).2.2.2.1, coe_f4RootGroup r01 fun c => (hl c).2.2.2.2.1,
    coe_f4RootGroup r01' fun c => (hl c).2.2.2.2.2, fun j hj => ?_⟩
  obtain ⟨m, hminj, hm⟩ := exists_sl2sl2ToF4 (K := GaloisField 2 f) (j := f4n j)
    (by rcases hj with rfl | rfl <;> decide)
  exact ⟨m, hminj, coe_f4RootGroup (isRoot_single .F4 (f4n j)) fun c => (hm c).2.2.1,
    coe_f4RootGroup (isRoot_neg_single .F4 (f4n j)) fun c => (hm c).2.2.2,
    fun c => ⟨(hm c).1.trans (hl c).1.symm, (hm c).2.1.trans (hl c).2.1.symm⟩⟩

theorem twistedE6C3LeviInput : TwistedE6C3LeviInput := by
  intro f hf
  obtain ⟨ι, hker, hι⟩ := exists_suToTwistedE6 (k := GaloisField 2 (2 * f))
    (card_galoisField_two_mul hf) (θ := Exceptional.frobQ 2 f) fun c => by
      rw [Exceptional.frobQ_apply, BorelTits.unitaryInvolution_apply]
  refine ⟨ι, hker, fun γ hγ => ?_⟩
  obtain ⟨h0, hr⟩ := c3PairRoots_check γ hγ
  have h := hι (c3Coords γ) hr
  rwa [c3ToF4_c3Coords h0] at h

open TwistedE6 Minuscule in
theorem twistedE6EdgeLeviInput : TwistedE6EdgeLeviInput := by
  intro f hf
  obtain ⟨l, hinj, hl⟩ := exists_sl3ToTwistedE6 hf
  have hε := frobQ_eq_iff_mem_range 2 f hf
  obtain ⟨f1, f1', f3, f3', f13, f13'⟩ := e6_fixed_check
  obtain ⟨r13, r13'⟩ := e6_root_check
  have p1 : TwistedE6.proj (sroot (e6n 1)) = ![1, 0, 0, 0] := by
    funext i; fin_cases i <;> rfl
  have p1' : TwistedE6.proj (-sroot (e6n 1)) = -![1, 0, 0, 0] := by
    funext i; fin_cases i <;> rfl
  have p3 : TwistedE6.proj (sroot (e6n 3)) = ![0, 1, 0, 0] := by
    funext i; fin_cases i <;> rfl
  have p3' : TwistedE6.proj (-sroot (e6n 3)) = -![0, 1, 0, 0] := by
    funext i; fin_cases i <;> rfl
  have p13 : TwistedE6.proj (sroot (e6n 1) + sroot (e6n 3)) = ![1, 1, 0, 0] := by
    funext i; fin_cases i <;> rfl
  have p13' : TwistedE6.proj (-(sroot (e6n 1) + sroot (e6n 3))) = -![1, 1, 0, 0] := by
    funext i; fin_cases i <;> rfl
  refine ⟨l, hinj,
    coe_twistedRootGroup_of_fixed hε (isRoot_single _ _) p1 f1 fun c => (hl c).1,
    coe_twistedRootGroup_of_fixed hε (isRoot_neg_single _ _) p1' f1' fun c => (hl c).2.1,
    coe_twistedRootGroup_of_fixed hε (isRoot_single _ _) p3 f3 fun c => (hl c).2.2.1,
    coe_twistedRootGroup_of_fixed hε (isRoot_neg_single _ _) p3' f3' fun c => (hl c).2.2.2.1,
    coe_twistedRootGroup_of_fixed hε (mem_rootFinset.1 r13) p13 f13 fun c => (hl c).2.2.2.2.1,
    coe_twistedRootGroup_of_fixed hε (mem_rootFinset.1 r13') p13' f13' fun c =>
      (hl c).2.2.2.2.2, fun j hj => ?_⟩
  obtain ⟨m₁, hm₁, hm₁v, hm₁r⟩ := exists_sl2FixedToTwistedE6 hf
  obtain ⟨a, b, hab, hp, hp', ha, hb⟩ : ∃ a b : Fin (Tag.rank .E6),
      ((a = nd 2 ∧ b = nd 4) ∨ (a = nd 0 ∧ b = nd 5)) ∧
        TwistedE6.proj (sroot a) = Pi.single j 1 ∧ TwistedE6.proj (-sroot a) = -Pi.single j 1 ∧
        a ∈ ({e6n 0, e6n 2, e6n 4, e6n 5} : Finset (Fin (Tag.rank .E6))) ∧
        b ∈ ({e6n 0, e6n 2, e6n 4, e6n 5} : Finset (Fin (Tag.rank .E6))) := by
    rcases hj with rfl | rfl
    · exact ⟨nd 2, nd 4, Or.inl ⟨rfl, rfl⟩, by funext i; fin_cases i <;> rfl,
        by funext i; fin_cases i <;> rfl, by decide, by decide⟩
    · exact ⟨nd 0, nd 5, Or.inr ⟨rfl, rfl⟩, by funext i; fin_cases i <;> rfl,
        by funext i; fin_cases i <;> rfl, by decide, by decide⟩
  obtain ⟨m₂, hm₂, hm₂v, hm₂r⟩ := exists_sl2PairToTwistedE6 hf hab
  have hc : ∀ x y, Commute (m₁ x) (m₂ y) := fun x y => by
    have hle : CurtisTits.rankOne (e6Data_valid.rootGroup (GaloisField 2 (2 * f))) a ⊔
        CurtisTits.rankOne (e6Data_valid.rootGroup (GaloisField 2 (2 * f))) b ≤
          Subgroup.centralizer
            (CurtisTits.rankOne (e6Data_valid.rootGroup (GaloisField 2 (2 * f))) (e6n 1) :
              Set (e6Data_valid.minGroup (GaloisField 2 (2 * f)))) :=
      sup_le (fun z hz => Subgroup.mem_centralizer_iff.2 fun w hw =>
          (commute_rankOne_one ha hw hz).eq)
        (fun z hz => Subgroup.mem_centralizer_iff.2 fun w hw =>
          (commute_rankOne_one hb hw hz).eq)
    exact Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      exact Subgroup.mem_centralizer_iff.1 (hle (hm₂r y)) _ (hm₁r x))
  have hrho : rho (sroot a) = sroot b := by
    rw [rho_single, rhoPerm_of_orbit hab]
  have hrho' : rho (-sroot a) = -sroot b := by
    rw [rho_neg_single, rhoPerm_of_orbit hab]
  have hne : rho (sroot a) ≠ sroot a := by
    rw [hrho]
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have hne' : rho (-sroot a) ≠ -sroot a := by
    rw [hrho']
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  refine ⟨m₁.noncommCoprod m₂ hc, injective_noncommCoprod_of_center hm₁ hm₂ hc
    fun b hb => LevisExtras.eq_one_of_mem_center_sl2 hb,
    coe_twistedRootGroup_of_pair (isRoot_single _ a) hp hne fun c => ?_,
    coe_twistedRootGroup_of_pair (isRoot_neg_single _ a) hp' hne' fun c => ?_,
    fun c => ⟨Subtype.ext ?_, Subtype.ext ?_⟩⟩
  · rw [MonoidHom.noncommCoprod_apply, map_one, one_mul, (hm₂v c).1, hrho, twistSign_single,
      Int.cast_one, one_mul]
  · rw [MonoidHom.noncommCoprod_apply, map_one, one_mul, (hm₂v c).2, hrho', twistSign_neg_single,
      Int.cast_one, one_mul]
  · rw [MonoidHom.noncommCoprod_apply, map_one, mul_one, (hm₁v c).1, (hl c).1]
  · rw [MonoidHom.noncommCoprod_apply, map_one, mul_one, (hm₁v c).2, (hl c).2.1]

end CFSG.Timmesfeld.LieEmbed
