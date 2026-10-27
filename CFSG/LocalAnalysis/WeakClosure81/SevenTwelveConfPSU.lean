module

public import CFSG.LocalAnalysis.WeakClosure81.SevenTwelveConfSUMain

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open CFSG.LocalAnalysis.WeakClosure81.SevenK

theorem statedSU_mul_self_of_rank_one {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = (2 ^ n) ^ 2) {m : ℕ} (g : ↥(StatedSU m (2 ^ n) F))
    (hg : Matrix.rank (((g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) - 1) = 1) : g * g = 1 := by
  haveI : CharP F 2 := charP_of_card_sq (p := 2) (f := n) hF
  let e : ↥(SUid (unitaryInvolution F 2 n) m) ≃* ↥(StatedSU m (2 ^ n) F) :=
    MulEquiv.subgroupCongr (SUid_eq_statedSU hF m)
  have h := suConf_mul_self_of_rank_one hF (e.symm g) hg
  calc g * g = e (e.symm g * e.symm g) := by rw [map_mul, MulEquiv.apply_symm_apply]
    _ = 1 := by rw [h, map_one]

theorem exists_sevenTwelveConfig_statedSU {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = (2 ^ n) ^ 2) (hn : 1 < n) {m : ℕ} (g : ↥(StatedSU m (2 ^ n) F))
    (hg : Matrix.rank (((g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) - 1) = 1) :
    ∃ (g₂ g₃ y : ↥(StatedSU m (2 ^ n) F)) (W T : Subgroup ↥(StatedSU m (2 ^ n) F)),
      SevenTwelveConfig (Subgroup.zpowers g) g₂ g₃ y W T := by
  haveI : CharP F 2 := charP_of_card_sq (p := 2) (f := n) hF
  let e : ↥(SUid (unitaryInvolution F 2 n) m) ≃* ↥(StatedSU m (2 ^ n) F) :=
    MulEquiv.subgroupCongr (SUid_eq_statedSU hF m)
  obtain ⟨g₂, g₃, y, W, T, h⟩ := exists_sevenTwelveConfig_suid hF hn (e.symm g) hg
  have h' := sevenTwelveConfig_mulEquiv e (suConf_mul_self_of_rank_one hF (e.symm g) hg) h
  rw [MulEquiv.apply_symm_apply] at h'
  exact ⟨_, _, _, _, _, h'⟩

theorem statedSU_ker_central_noinv {F : Type} [Field F] [CharP F 2] {m q : ℕ} :
    (QuotientGroup.mk' ((StatedScalars (Fin m) F).subgroupOf (StatedSU m q F)) :
        ↥(StatedSU m q F) →* StatedProj (StatedSU m q F)).ker ≤
        Subgroup.center ↥(StatedSU m q F) ∧
      ∀ z ∈ (QuotientGroup.mk' ((StatedScalars (Fin m) F).subgroupOf (StatedSU m q F)) :
        ↥(StatedSU m q F) →* StatedProj (StatedSU m q F)).ker, z * z = 1 → z = 1 := by
  have hker : ∀ z : ↥(StatedSU m q F),
      z ∈ (QuotientGroup.mk' ((StatedScalars (Fin m) F).subgroupOf (StatedSU m q F)) :
        ↥(StatedSU m q F) →* StatedProj (StatedSU m q F)).ker ↔
        (z : GL (Fin m) F) ∈ (Matrix.GeneralLinearGroup.scalar (Fin m)).range := by
    intro z
    rw [QuotientGroup.ker_mk', Subgroup.mem_subgroupOf, StatedScalars]
  constructor
  · intro z hz
    obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp ((hker z).mp hz)
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    show (w : GL (Fin m) F) * (z : GL (Fin m) F) = (z : GL (Fin m) F) * (w : GL (Fin m) F)
    rw [← hc]
    exact (Matrix.GeneralLinearGroup.scalar_commute c (w : GL (Fin m) F)).symm
  · intro z hz hzz
    obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp ((hker z).mp hz)
    rcases isEmpty_or_nonempty (Fin m) with _ | hne
    · exact Subtype.ext (Units.ext
        (Subsingleton.elim ((z : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) 1))
    · obtain ⟨i⟩ := hne
      have hsq : Matrix.GeneralLinearGroup.scalar (Fin m) c *
          Matrix.GeneralLinearGroup.scalar (Fin m) c = 1 := by
        have h : (z : GL (Fin m) F) * (z : GL (Fin m) F) = 1 := by
          simpa using congrArg (fun x : ↥(StatedSU m q F) => (x : GL (Fin m) F)) hzz
        rw [← hc] at h
        exact h
      have hval : ((c * c : Fˣ) : F) = 1 := by
        have h := congrArg (fun x : GL (Fin m) F => (x : Matrix (Fin m) (Fin m) F) i i)
          (show Matrix.GeneralLinearGroup.scalar (Fin m) (c * c) = 1 by rw [map_mul]; exact hsq)
        simpa [Matrix.GeneralLinearGroup.coe_scalar] using h
      have hcsq : c * c = 1 := Units.ext hval
      have hc1 : c = 1 := by
        have hsq2 : ((c : F) ^ 2) = ((1 : F) ^ 2) := by
          have h := congrArg (fun u : Fˣ => (u : F)) hcsq
          simpa [pow_two] using h
        exact Units.ext (CharTwo.sq_inj.mp hsq2)
      have hz1 : (z : GL (Fin m) F) = 1 := by rw [← hc, hc1, map_one]
      exact Subtype.ext hz1

theorem exists_sevenTwelveConfig_statedProj {F : Type} [Field F] [Finite F] {n m : ℕ}
    (hF : Nat.card F = (2 ^ n) ^ 2) (hn : 1 < n) {x : StatedProj (StatedSU m (2 ^ n) F)}
    (hx : IsUnitaryTransvectionIn m n x) :
    ∃ (g₂ g₃ y : StatedProj (StatedSU m (2 ^ n) F))
      (W T : Subgroup (StatedProj (StatedSU m (2 ^ n) F))),
      SevenTwelveConfig (Subgroup.zpowers x) g₂ g₃ y W T := by
  haveI : CharP F 2 := charP_of_card_sq (p := 2) (f := n) hF
  obtain ⟨g, rfl, hg⟩ := hx
  obtain ⟨g₂, g₃, y, W, T, h⟩ := exists_sevenTwelveConfig_statedSU hF hn g hg
  obtain ⟨hcen, hinv⟩ := statedSU_ker_central_noinv (F := F) (m := m) (q := 2 ^ n)
  exact ⟨_, _, _, _, _, sevenTwelveConfig_map (QuotientGroup.mk' _)
    (QuotientGroup.mk'_surjective _) hcen hinv (statedSU_mul_self_of_rank_one hF g hg) h⟩

end CFSG.LocalAnalysis.WeakClosure81

end
