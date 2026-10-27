module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ResA7
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModM10

public section

set_option linter.unusedSectionVars false

namespace CFSG.Quasithin.F53Mod

open Equiv

theorem exists_conj_threeCyc : ∃ g : Perm (Fin 5), g * threeCyc012 * g⁻¹ = threeCyc234 := by
  unfold threeCyc012 threeCyc234
  decide +kernel

theorem alt5_le_sup_conj (g : Perm (Fin 5)) (hg : g * threeCyc012 * g⁻¹ = threeCyc234) :
    alternatingGroup (Fin 5) ≤ Subgroup.zpowers threeCyc012 ⊔
      (Subgroup.zpowers threeCyc012).map (MulAut.conj g).toMonoidHom := by
  refine alt5_le_closure_threeCycles.trans ((Subgroup.closure_le _).mpr ?_)
  rintro _ (rfl | rfl)
  · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  · refine Subgroup.mem_sup_right ⟨threeCyc012, Subgroup.mem_zpowers _, ?_⟩
    simpa using hg


theorem model_iso_orth (M : Model 5) (hnt : ∃ w : M.W, w ≠ 1)
    (hidx : idx M threeCyc012 ≤ 4) (hb : commW M (alternatingGroup (Fin 5)) ⊤ = ⊤) :
    Nonempty (M.Iso orth) := by
  classical
  set Mb := M.modA5 with hMb
  set A5 := alternatingGroup (Fin 5) with hA5
  have hbnt : ∃ w : Mb.W, w ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hall : ∀ w : M.W, w ∈ fixW M A5 := fun w => (M.projA5_eq_one_iff w).mp (hcon _)
    have h0 : commW M A5 ⊤ = ⊥ := by
      rw [commW_eq_bot_iff]
      intro b hb' u _
      exact hall u b hb'
    rw [hb] at h0
    obtain ⟨w, hw⟩ := hnt
    have : w ∈ (⊥ : Subgroup M.W) := h0 ▸ Subgroup.mem_top w
    exact hw (Subgroup.mem_bot.mp this)
  have hfix5 : fixW Mb A5 = ⊥ :=
    fixW_quot_alt5_eq_bot M (isInvSub_fixW_of_normal M alternatingGroup.normal)
  have hfixtop : fixW Mb ⊤ = ⊥ := Model.fixW_modA5_top M
  have hidxb : idx Mb threeCyc012 ≤ 4 := by
    refine le_trans ?_ hidx
    unfold idx
    rw [Model.index_fixW_modA5]
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero)
      (Subgroup.index_dvd_of_le (fixW_le_fixQ _ _))
  obtain ⟨g, hg⟩ := exists_conj_threeCyc
  have hcard : Nat.card Mb.W ≤ 16 := by
    have h1 := card_le_fidx_sq Mb g (alt5_le_sup_conj g hg) hfix5
    have h2 : (fixW Mb (Subgroup.zpowers threeCyc012)).index ≤ 4 := hidxb
    calc Nat.card Mb.W ≤ (fixW Mb (Subgroup.zpowers threeCyc012)).index ^ 2 := h1
      _ ≤ 4 ^ 2 := Nat.pow_le_pow_left h2 2
      _ = 16 := by norm_num
  obtain ⟨e⟩ : Nonempty (Mb.Iso orth) := by
    rcases iso_of_card_le_sixteen Mb hbnt hfixtop hcard with h | h
    · exact h
    · exfalso
      obtain ⟨e⟩ := h
      have h1 := e.idx_eq threeCyc012
      have h2 : idx nat threeCyc012 = 16 := by
        rw [idx_nat]
        have e1 : threeCyc012 ≠ 1 := by unfold threeCyc012; decide +kernel
        have e2 : threeCyc012 ^ 2 ≠ 1 := by unfold threeCyc012; decide +kernel
        have e3 : threeCyc012 ^ 3 = 1 := by unfold threeCyc012; decide +kernel
        simp only [e1, e2, e3, ↓reduceIte]
      omega
  let π : M.W →* orth.W := e.toMulEquiv.toMonoidHom.comp M.projA5
  have hπs : Function.Surjective π := e.toMulEquiv.surjective.comp M.projA5_surjective
  have hπe : ∀ σ w, π (M.act σ w) = orth.act σ (π w) := by
    intro σ w
    show e.toMulEquiv (M.projA5 (M.act σ w)) = orth.act σ (e.toMulEquiv (M.projA5 w))
    rw [← M.projA5_act, e.map_act]
  have hker : ∀ w, π w = 1 → ∀ σ ∈ A5, M.act σ w = w := by
    intro w hw σ hσ
    have h1 : e.toMulEquiv (M.projA5 w) = 1 := hw
    have h2 : M.projA5 w = 1 := e.toMulEquiv.injective (by rw [h1, map_one])
    exact ((M.projA5_eq_one_iff w).mp h2) σ hσ
  obtain ⟨s, hπs', hse⟩ := exists_section M π hπs (fun σ _ w => hπe σ w) hker
  have hrange : ∀ u : M.W, π (u * (s (π u))⁻¹) = 1 := by
    intro u
    rw [map_mul, map_inv, hπs', mul_inv_cancel]
  have hsurj : Function.Surjective s := by
    have hle : (⊤ : Subgroup M.W) ≤ s.range := by
      rw [← hb]
      refine (Subgroup.closure_le _).mpr ?_
      rintro _ ⟨b, hbA, u, -, rfl⟩
      have hu1 := hrange u
      refine ⟨orth.act b (π u) * (π u)⁻¹, ?_⟩
      rw [map_mul, map_inv, ← hse b hbA (π u)]
      obtain ⟨t, ht⟩ : ∃ t, t = s (π u) := ⟨_, rfl⟩
      rw [← ht] at hu1 ⊢
      obtain ⟨f, hf⟩ : ∃ f, f = u * t⁻¹ := ⟨_, rfl⟩
      rw [← hf] at hu1
      have hfix := hker f hu1 b hbA
      have hu : f * t = u := by rw [hf]; group
      calc M.act b t * t⁻¹ = (f * f⁻¹) * (M.act b t * t⁻¹) := by rw [mul_inv_cancel, one_mul]
        _ = M.act b f * M.act b t * (f * t)⁻¹ := by rw [hfix, mul_inv_rev]; ac_rfl
        _ = M.act b (f * t) * (f * t)⁻¹ := by rw [map_mul]
        _ = M.act b u * u⁻¹ := by rw [hu]
    intro u
    exact hle (Subgroup.mem_top u)
  have hinj : Function.Injective π := by
    intro w w' hww
    obtain ⟨a, rfl⟩ := hsurj w
    obtain ⟨a', rfl⟩ := hsurj w'
    rw [hπs', hπs'] at hww
    rw [hww]
  exact ⟨⟨MulEquiv.ofBijective π ⟨hinj, hπs⟩, hπe⟩⟩

end CFSG.Quasithin.F53Mod
