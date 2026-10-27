module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22d
public import CFSG.LocalAnalysis.UniquenessCase.UCKPRank1
public import CFSG.LocalAnalysis.UniquenessCase.UC22S22c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

namespace P22fin

theorem isL2Ev_of_isL2 {X : Type} [Group X] {n : ℕ} (h : IsL2 X n) : IsL2Ev X n ∧ 2 ≤ n := by
  obtain ⟨⟨-, hn1, -, hne, -⟩, F, _, _, hF, ⟨e⟩⟩ :=
    CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) h
  haveI : CharP F 2 := uc22p22d_charP_two hn1 hF
  have hZ := CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSL_two_eq_bot (K := F)
  let g : StatedProj (StatedSL 2 F) ≃* StatedSL 2 F :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  refine ⟨⟨F, inferInstance, inferInstance, hF, ⟨e.trans g⟩⟩, ?_⟩
  by_contra hlt
  obtain rfl : n = 1 := by omega
  exact hne (by norm_num)

theorem isL2Ev_of_mulEquiv {X Y : Type} [Group X] [Group Y] {n : ℕ} (h : IsL2Ev X n)
    (e : X ≃* Y) : IsL2Ev Y n := by
  obtain ⟨F, hF1, hF2, hF, ⟨f⟩⟩ := h
  exact ⟨F, hF1, hF2, hF, ⟨e.symm.trans f⟩⟩

theorem card_le_sq_of_commute {Y : Type*} [Group Y] [Finite Y] {p : ℕ} [Fact p.Prime]
    {A B E : Subgroup Y} (hc : ∀ a ∈ A, ∀ b ∈ B, Commute a b) (hi : A ⊓ B = ⊥)
    (hA : ∀ S : Sylow p A, IsCyclic S) (hB : ∀ S : Sylow p B, IsCyclic S)
    (hE : IsElemAbelian p E) (hEAB : E ≤ A ⊔ B) : Nat.card E ≤ p ^ 2 := by
  classical
  have hcomm : ∀ (a : A) (b : B), Commute (A.subtype a) (B.subtype b) :=
    fun a b => hc a a.2 b b.2
  let f : A × B →* Y := MonoidHom.noncommCoprod A.subtype B.subtype hcomm
  have hinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨a, b⟩ hab
    rw [MonoidHom.mem_ker] at hab
    change (a : Y) * (b : Y) = 1 at hab
    have hab' : (a : Y) = (b : Y)⁻¹ := eq_inv_of_mul_eq_one_left hab
    have haB : (a : Y) ∈ B := hab' ▸ inv_mem b.2
    have ha1 : (a : Y) = 1 := by
      have : (a : Y) ∈ A ⊓ B := ⟨a.2, haB⟩
      rwa [hi, Subgroup.mem_bot] at this
    have hb1 : (b : Y) = 1 := by
      rw [ha1, eq_comm, inv_eq_one] at hab'
      exact hab'
    exact Subgroup.mem_bot.2 (Prod.ext (Subtype.ext ha1) (Subtype.ext hb1))
  have hrange : f.range = A ⊔ B := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  have hFel : IsElemAbelian p (E.comap f) := hE.comap hinj
  have hcardF : Nat.card (E.comap f) = Nat.card E := by
    rw [← Subgroup.card_map_of_injective hinj, Subgroup.map_comap_eq_self (hrange ▸ hEAB)]
  have h₁ : Nat.card ((E.comap f).map (MonoidHom.fst A B)) ≤ p :=
    UCK.card_le_of_sylow_isCyclic hA (hFel.map _)
  have h₂ : Nat.card ((E.comap f).map (MonoidHom.snd A B)) ≤ p :=
    UCK.card_le_of_sylow_isCyclic hB (hFel.map _)
  have hle : E.comap f ≤ ((E.comap f).map (MonoidHom.fst A B)).prod
      ((E.comap f).map (MonoidHom.snd A B)) := fun x hx => ⟨⟨x, hx, rfl⟩, ⟨x, hx, rfl⟩⟩
  calc Nat.card E = Nat.card (E.comap f) := hcardF.symm
    _ ≤ Nat.card (((E.comap f).map (MonoidHom.fst A B)).prod
          ((E.comap f).map (MonoidHom.snd A B))) := Subgroup.card_le_of_le hle
    _ = Nat.card ((E.comap f).map (MonoidHom.fst A B)) *
          Nat.card ((E.comap f).map (MonoidHom.snd A B)) := by
      rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod]
    _ ≤ p * p := Nat.mul_le_mul h₁ h₂
    _ = p ^ 2 := (sq p).symm

theorem le_pElementSubgroup_of_elemAbelian {Y : Type} [Group Y] {p : ℕ} (hp : p.Prime)
    {E : Subgroup Y} (hE : IsElemAbelian p E) :
    E ≤ CFSG.RankThree.PartOne.pElementSubgroup p ⊤ := by
  intro x hx
  apply Subgroup.subset_closure
  refine ⟨Subgroup.mem_top x, ?_⟩
  rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one (hE.2 x hx)) with h | h
  · exact ⟨0, by rw [h, pow_zero]⟩
  · exact ⟨1, by rw [h, pow_one]⟩

end P22fin

end CFSG.LocalAnalysis.UniquenessCase.UC22
