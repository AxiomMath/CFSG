module

public import CFSG.RankThree.PartTwo.Sec21.FF81Am4Model
public import CFSG.RankThree.PartTwo.Sec21.FF81Defs
import CFSG.ClassicalInvolution.Q3.Q3VCtMain
import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviSp6

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.Assembly.LowTwoRank (StatedSp StatedLieAdmissible)
open CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.SeitzReduction.SymplecticPilot
open CFSG.LieType.Universal CFSG.LieType.CurtisTits
open CFSG.ClassicalInvolution.WeakCT (blk)
open scoped MatrixGroups

namespace Am4

theorem center_sp4_zmod2_eq_bot : Subgroup.center (StatedSp 4 (ZMod 2)) = ⊥ := by
  rw [CFSG.LieType.Universal.Symplectic.center_eq,
    CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot]

end Am4

section CT4G


theorem hasLeviAmalgam_of_mulEquiv {Y : Type} [Group Y] (e : Sp8.K ≃* Y) :
    HasLeviAmalgam Sp8 Y := by
  have hadm : StatedLieAdmissible .PSp 4 2 1 := ⟨Nat.prime_two, le_rfl, by decide, by decide⟩
  have hCT := CFSG.LieType.CurtisTits.curtisTitsConclusion_symplectic.{0} (n := 4)
    (F := GaloisField 2 1) hadm (GaloisField.card 2 1 one_ne_zero) (by norm_num)
  have hgen : ⨆ J, Sp8.D.leviAmalgam J = ⊤ := hCT.1.1
  refine ⟨fun J => (Sp8.D.leviAmalgam J).map e.toMonoidHom,
    fun J => e.subgroupMap (Sp8.D.leviAmalgam J), ?_, ?_⟩
  · rw [← Subgroup.map_iSup, hgen, Subgroup.map_top_of_surjective _ e.surjective]
  · intro I J _ x y hxy
    show e (x : Sp8.K) = e (y : Sp8.K)
    rw [hxy]

theorem nonempty_sp8_mulEquiv {Y : Type} [Group Y] (Ψ : StatedSp 4 (ZMod 2) →* Y)
    (hs : Function.Surjective Ψ) (hk : Ψ.ker ≤ Subgroup.center (StatedSp 4 (ZMod 2))) :
    Nonempty (Sp8.K ≃* Y) := by
  have hinj : Function.Injective Ψ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    exact le_antisymm (hk.trans Am4.center_sp4_zmod2_eq_bot.le) bot_le
  haveI : Fintype (GaloisField 2 1) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 2 1) = 2 := by
    rw [← Nat.card_eq_fintype_card]; simpa using GaloisField.card 2 1 one_ne_zero
  let r : ZMod 2 ≃+* GaloisField 2 1 :=
    ZMod.ringEquivOfPrime (GaloisField 2 1) Nat.prime_two hcard
  exact ⟨(CFSG.SeitzReduction.F4Pilot.statedSpCongr r.symm 4).trans
    (MulEquiv.ofBijective Ψ ⟨hinj, hs⟩)⟩

theorem hasLeviAmalgam_of_glue {X : Type} [Group X] (θL θM : Am4.K3 →* X)
    (hL : Function.Injective θL) (hM : Function.Injective θM)
    (ha : ∀ A, θL (Am4.ι₁ A) = θM (Am4.ι₀ A))
    (hb : ∀ A B, θM (Am4.ι₁ A) * θL (Am4.ι₀ B) = θL (Am4.ι₀ B) * θM (Am4.ι₁ A))
    (hc0 : ∀ A B, θM (Am4.ι₂ A) * θL (Am4.ι₀ B) = θL (Am4.ι₀ B) * θM (Am4.ι₂ A))
    (hc1 : ∀ A B, θM (Am4.ι₂ A) * θL (Am4.ι₁ B) = θL (Am4.ι₁ B) * θM (Am4.ι₂ A))
    (hgen : (θL.comp Am4.ι₀).range ⊔ (θL.comp Am4.ι₁).range ⊔ (θM.comp Am4.ι₁).range ⊔
      (θM.comp Am4.ι₂).range = ⊤) :
    HasLeviAmalgam Sp8 X := by
  obtain ⟨κ, hκ0, hκ1⟩ := Am4.exists_kappa
  have hadm : StatedLieAdmissible .PSp 4 2 1 := ⟨Nat.prime_two, le_rfl, by decide, by decide⟩
  let ρ : Fin 4 → SL(2, ZMod 2) →* X :=
    ![θL.comp Am4.ι₀, θL.comp Am4.ι₁, θM.comp Am4.ι₁, θM.comp Am4.ι₂]
  let ψ : ∀ i : Fin 4, i.val + 2 < 4 → SL(3, ZMod 2) →* X :=
    fun i _ => if i.val = 0 then θL.comp κ else θM.comp κ
  have hψ0 : ∀ (i : Fin 4) (h : i.val + 2 < 4),
      (ψ i h).comp (blk (ZMod 2) 0) = ρ ⟨i.val + 1, by omega⟩ := by
    intro i h
    have hi : i.val = 0 ∨ i.val = 1 := by omega
    rcases hi with hi | hi
    · obtain rfl : i = 0 := Fin.ext hi
      show (θL.comp κ).comp (blk (ZMod 2) 0) = θL.comp Am4.ι₁
      rw [MonoidHom.comp_assoc, hκ0]
    · obtain rfl : i = 1 := Fin.ext hi
      show (θM.comp κ).comp (blk (ZMod 2) 0) = θM.comp Am4.ι₁
      rw [MonoidHom.comp_assoc, hκ0]
  have hψ1 : ∀ (i : Fin 4) (h : i.val + 2 < 4), (ψ i h).comp (blk (ZMod 2) 1) = ρ i := by
    intro i h
    have hi : i.val = 0 ∨ i.val = 1 := by omega
    rcases hi with hi | hi
    · obtain rfl : i = 0 := Fin.ext hi
      show (θL.comp κ).comp (blk (ZMod 2) 1) = θL.comp Am4.ι₀
      rw [MonoidHom.comp_assoc, hκ1]
    · obtain rfl : i = 1 := Fin.ext hi
      show (θM.comp κ).comp (blk (ZMod 2) 1) = θL.comp Am4.ι₁
      rw [MonoidHom.comp_assoc, hκ1]
      exact MonoidHom.ext fun A => (ha A).symm
  have hgen' : ⨆ k, (ρ k).range = ⊤ := by
    rw [eq_top_iff, ← hgen]
    exact sup_le (sup_le (sup_le (le_iSup (fun k => (ρ k).range) 0)
      (le_iSup (fun k => (ρ k).range) 1)) (le_iSup (fun k => (ρ k).range) 2))
      (le_iSup (fun k => (ρ k).range) 3)
  have hcomm : ∀ i j : Fin 4, i.val + 1 < j.val → ∀ a ∈ (ρ i).range, ∀ b ∈ (ρ j).range,
      a * b = b * a := by
    intro i j hij a ha' b hb'
    fin_cases i <;> fin_cases j <;> simp at hij
    · obtain ⟨A, rfl⟩ := ha'
      obtain ⟨B, rfl⟩ := hb'
      exact (hb B A).symm
    · obtain ⟨A, rfl⟩ := ha'
      obtain ⟨B, rfl⟩ := hb'
      exact (hc0 B A).symm
    · obtain ⟨A, rfl⟩ := ha'
      obtain ⟨B, rfl⟩ := hb'
      exact (hc1 B A).symm
  have hρ : ∀ k, Function.Injective (ρ k) ∧ (ρ k).range = (ρ k).range := by
    intro k
    fin_cases k
    · exact ⟨hL.comp Am4.ι₀_injective, rfl⟩
    · exact ⟨hL.comp Am4.ι₁_injective, rfl⟩
    · exact ⟨hM.comp Am4.ι₁_injective, rfl⟩
    · exact ⟨hM.comp Am4.ι₂_injective, rfl⟩
  have hψ4l : (θM.comp Am4.lam).comp (CFSG.ClassicalInvolution.WeakCT.spBlock (ZMod 2) 1) =
      ρ ⟨4 - 1, by omega⟩ := by
    show (θM.comp Am4.lam).comp (CFSG.ClassicalInvolution.WeakCT.spBlock (ZMod 2) 1) =
      θM.comp Am4.ι₂
    rw [MonoidHom.comp_assoc, Am4.lam_comp_spBlock_one]
  have hψ4s : (θM.comp Am4.lam).comp (CFSG.ClassicalInvolution.WeakCT.spBlock (ZMod 2) 0) =
      ρ ⟨4 - 2, by omega⟩ := by
    show (θM.comp Am4.lam).comp (CFSG.ClassicalInvolution.WeakCT.spBlock (ZMod 2) 0) =
      θM.comp Am4.ι₁
    rw [MonoidHom.comp_assoc, Am4.lam_comp_spBlock_zero]
  obtain ⟨Ψ, hs, hk, -⟩ := CFSG.ClassicalInvolution.Q3.Q3V.weakCT_symplectic_of_family
    (n := 4) (p := 2) (f := 1) hadm (by norm_num) (F := ZMod 2) (by simp)
    (X := X) (fun k => (ρ k).range) hgen' hcomm ρ hρ ψ hψ0 hψ1 (θM.comp Am4.lam) hψ4l hψ4s
  exact hasLeviAmalgam_of_mulEquiv (nonempty_sp8_mulEquiv Ψ hs hk).some

theorem hasLeviAmalgam_of_glue_sub {G : Type} [Group G] (Y : Subgroup G) (θL θM : Am4.K3 →* G)
    (hLY : ∀ x, θL x ∈ Y) (hMY : ∀ x, θM x ∈ Y)
    (hL : Function.Injective θL) (hM : Function.Injective θM)
    (ha : ∀ A, θL (Am4.ι₁ A) = θM (Am4.ι₀ A))
    (hb : ∀ A B, θM (Am4.ι₁ A) * θL (Am4.ι₀ B) = θL (Am4.ι₀ B) * θM (Am4.ι₁ A))
    (hc0 : ∀ A B, θM (Am4.ι₂ A) * θL (Am4.ι₀ B) = θL (Am4.ι₀ B) * θM (Am4.ι₂ A))
    (hc1 : ∀ A B, θM (Am4.ι₂ A) * θL (Am4.ι₁ B) = θL (Am4.ι₁ B) * θM (Am4.ι₂ A))
    (hgen : (θL.comp Am4.ι₀).range ⊔ (θL.comp Am4.ι₁).range ⊔ (θM.comp Am4.ι₁).range ⊔
      (θM.comp Am4.ι₂).range = Y) :
    HasLeviAmalgam Sp8 ↥Y := by
  refine hasLeviAmalgam_of_glue (θL.codRestrict Y hLY) (θM.codRestrict Y hMY)
    (fun x y h => hL (congrArg Subtype.val h)) (fun x y h => hM (congrArg Subtype.val h))
    (fun A => Subtype.ext ?_) (fun A B => Subtype.ext ?_) (fun A B => Subtype.ext ?_)
    (fun A B => Subtype.ext ?_) ?_
  · exact ha A
  · exact hb A B
  · exact hc0 A B
  · exact hc1 A B
  · apply Subgroup.map_injective Y.subtype_injective
    have e : ∀ (θ : Am4.K3 →* G) (h : ∀ x, θ x ∈ Y) (ι : SL(2, ZMod 2) →* Am4.K3),
        Subgroup.map Y.subtype ((θ.codRestrict Y h).comp ι).range = (θ.comp ι).range := by
      intro θ h ι
      rw [← MonoidHom.range_comp]
      rfl
    rw [Subgroup.map_sup, Subgroup.map_sup, Subgroup.map_sup, e, e, e, e, hgen,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]

end CT4G

end CFSG.RankThree.PartTwo.Sec21.FF81
