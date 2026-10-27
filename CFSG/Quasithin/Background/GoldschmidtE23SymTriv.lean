module

public import CFSG.Quasithin.Background.GoldschmidtE23SymJ

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank G6 Equiv

namespace GE23

theorem vecOf_comm (σ : Perm (Fin 5)) (y : ↥(coreMod 5)) (j : Fin 5) :
    vecOf (coreAct 5 σ y * y⁻¹) j = vecOf y (σ⁻¹ j) - vecOf y j := by
  have h1 : vecOf (coreAct 5 σ y * y⁻¹) j = vecOf (coreAct 5 σ y) j + - vecOf y j := rfl
  rw [h1, vecOf_coreAct, sub_eq_add_neg]
  rfl

theorem fixed_eps_core (y : ↥(coreMod 5)) (h : coreAct 5 (sa * sb) y = y) :
    coreAct 5 sa y = y ∧ coreAct 5 sb y = y := by
  obtain ⟨h1, h2⟩ := fixed_eps (vecOf y) (sum_vecOf y) ((coreAct_eq_iff).1 h)
  exact ⟨(coreAct_eq_iff).2 h1, (coreAct_eq_iff).2 h2⟩

theorem comm_eps_core (y : ↥(coreMod 5)) :
    coreAct 5 sa (coreAct 5 (sa * sb) y * y⁻¹) = coreAct 5 (sa * sb) y * y⁻¹ ∧
    coreAct 5 sb (coreAct 5 (sa * sb) y * y⁻¹) = coreAct 5 (sa * sb) y * y⁻¹ := by
  obtain ⟨h1, h2⟩ := comm_eps (vecOf y) (sum_vecOf y)
  refine ⟨(coreAct_eq_iff).2 fun i => ?_, (coreAct_eq_iff).2 fun i => ?_⟩
  · rw [vecOf_comm, vecOf_comm]
    exact (h1 i).symm
  · rw [vecOf_comm, vecOf_comm]
    exact (h2 i).symm

theorem fixed_of_e4 {y : ↥(coreMod 5)} (ha : coreAct 5 sa y = y) (hb : coreAct 5 sb y = y) :
    ∀ τ ∈ e4, coreAct 5 τ y = y := by
  intro τ hτ
  refine Subgroup.closure_induction (p := fun x _ => coreAct 5 x y = y) ?_ ?_ ?_ ?_ hτ
  · intro x hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  · simp
  · intro a b _ _ hA hB
    rw [map_mul, MulAut.mul_apply, hB, hA]
  · intro a _ hA
    rw [map_inv]
    calc (coreAct 5 a)⁻¹ y = (coreAct 5 a)⁻¹ (coreAct 5 a y) := by rw [hA]
      _ = y := MulAut.inv_apply_self _ _ _

section Triv

variable {V : Type} [CommGroup V] [Finite V] {X T M : Subgroup (MulAut V)}
  {Ps : Set (Subgroup (MulAut V))}
  {ψ : Subgroup (MulAut V) → Perm (Fin 5) →* MulAut V}
  {β : Subgroup (MulAut V) → ↥(coreMod 5) →* V}

namespace SymData

variable (hD : SymData X T M Ps ψ β)

include hD

theorem trivial_action :
    ∀ x ∈ T ⊓ centSub (fixV (ffJP Ps T)), ∀ v : V, x v * v⁻¹ ∈ fixV (ffJP Ps T) := by
  classical
  intro x hx
  have hsc := hD.ctx.sc
  have hfam := hD.fam
  set J := ffJP Ps T with hJdef
  set I := B69.blkFamily X with hI
  have hJeq : J = ⨆ H ∈ I, e4.map (ψ H) := hD.ffJP_eq
  have hxT : x ∈ T := hx.1
  have hxX : x ∈ X := hD.ctx.hmp.isSylow.1 hxT
  have hxcent : ∀ z ∈ fixV J, x z = z := fun z hz => mem_centSub.1 hx.2 z hz
  have hfixJ : ∀ z : V, (∀ H ∈ I, ∀ p ∈ e4.map (ψ H), p z = z) → z ∈ fixV J := by
    intro z hz
    have : J ≤ MulAction.stabilizer (MulAut V) z := by
      rw [hJeq]
      exact iSup₂_le fun H hH p hp => hz H hH p hp
    exact fun y hy => this hy
  have hsplit : ∀ H ∈ I, ∀ v : V, ∃ w ∈ commV H, ∃ c ∈ fixV H, v = w * c := by
    intro H hH v
    obtain ⟨w, hw, c, hc, hv⟩ := blocks_split hD.ctx.hB hD.ctx.hmp hD.ctx.hFF hD.ctx.hk2 {H}
      (fun H' hH' => by rw [Finset.mem_singleton.1 hH']; exact hH) v
    refine ⟨w, ?_, c, ?_, hv⟩
    · simpa using hw
    · simpa using hc
  have hblock : ∀ H ∈ I, ∃ a : MulAut V, x * a = a * x ∧ (∀ v : V, a v * v⁻¹ ∈ fixV J) ∧
      ∀ v : V, a v = v → ∀ p ∈ e4.map (ψ H), p v = v := by
    intro H hH
    have hS := hD.spec H hH
    have hxH : B6.conjSub x H = H := by
      by_contra hne
      have hz1 : β H y0 ≠ 1 := fun h => y0_ne_one (hS.β_inj (by rw [h, map_one]))
      have hzW : β H y0 ∈ commV H := hS.β_mem y0
      have hzJ : β H y0 ∈ fixV J := by
        refine hfixJ _ fun H' hH' p hp => ?_
        by_cases hHH : H' = H
        · have hp' : p ∈ e4.map (ψ H) := hHH ▸ hp
          obtain ⟨τ, hτ, rfl⟩ := Subgroup.mem_map.1 hp'
          rw [← hS.equiv, fixed_of_e4 y0_fixed_sa y0_fixed_sb τ hτ]
        · exact hfam.hother H hH H' hH' hHH p (hfam.map_le hH' _ hp) _ hzW
      have hxz : x (β H y0) = β H y0 := hxcent _ hzJ
      have hH'I : B6.conjSub x H ∈ I := by
        obtain ⟨L, hL, rfl⟩ := B69.mem_blkFamily.1 hH
        have hc : CFSG.Open.IsComponentOf (B6.conjSub x L) X := B113.isComponentOf_conj hL hxX
        exact B69.mem_blkFamily.2 ⟨_, hc, B69.conjSub_blk hxX⟩
      have hzH' : β H y0 ∈ commV (B6.conjSub x H) := by
        rw [show B6.conjSub x H = H.map (MulAut.conj x).toMonoidHom from rfl,
          B19.commV_map_conj x H]
        exact ⟨β H y0, hzW, hxz⟩
      have hmem : β H y0 ∈ commV H ⊓ ⨆ H' ∈ I, ⨆ (_ : H' ≠ H), commV H' :=
        ⟨hzW, le_iSup₂_of_le (f := fun H' (_ : H' ∈ I) => ⨆ (_ : H' ≠ H), commV H')
          (B6.conjSub x H) hH'I (le_iSup_of_le hne le_rfl) hzH'⟩
      rw [hfam.hind0 H hH, Subgroup.mem_bot] at hmem
      exact hz1 hmem
    have hxH2 : B6.conjSub x⁻¹ H ≤ H := by
      have : B6.conjSub x⁻¹ H = H := by
        calc B6.conjSub x⁻¹ H = B6.conjSub x⁻¹ (B6.conjSub x H) := by rw [hxH]
          _ = H := B69.conjSub_inv_conjSub x H
      exact this.le
    have hxH' : x ∈ Subgroup.normalizer (H : Set (MulAut V)) :=
      B6.mem_normalizer_of_conjSub_le hxH.le hxH2
    have hconjD : ∀ d ∈ T ⊓ H, x * d * x⁻¹ ∈ T ⊓ H := fun d hd =>
      ⟨T.mul_mem (T.mul_mem hxT hd.1) (T.inv_mem hxT),
        (Subgroup.mem_normalizer_iff.1 hxH' d).1 hd.2⟩
    have hconjD' : ∀ d ∈ T ⊓ H, x⁻¹ * d * x ∈ T ⊓ H := fun d hd =>
      ⟨T.mul_mem (T.mul_mem (T.inv_mem hxT) hd.1) hxT, by
        have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hxH') d).1 hd.2
        simpa using this⟩
    have haD : ψ H (sa * sb) ∈ T ⊓ H := by
      rw [hS.syl]
      exact Subgroup.mem_map_of_mem _ (d8.mul_mem sa_mem_d8 sb_mem_d8)
    have hcommx : x * ψ H (sa * sb) = ψ H (sa * sb) * x := by
      have h1 := hconjD _ haD
      rw [hS.syl] at h1
      obtain ⟨σ, hσ, hσa⟩ := Subgroup.mem_map.1 h1
      have hσc : ∀ τ ∈ d8list, σ * τ = τ * σ := by
        intro τ hτ
        have hτd : τ ∈ d8 := mem_d8_iff.2 hτ
        have hψτ : ψ H τ ∈ T ⊓ H := by
          rw [hS.syl]
          exact Subgroup.mem_map_of_mem _ hτd
        have h2 := hconjD' _ hψτ
        rw [hS.syl] at h2
        obtain ⟨τ', hτ'd, hτ'⟩ := Subgroup.mem_map.1 h2
        apply hS.ψ_inj
        rw [map_mul, map_mul, hσa]
        have e1 : ψ H τ = x * ψ H τ' * x⁻¹ := by rw [hτ']; group
        have hcomm' : ψ H (sa * sb) * ψ H τ' = ψ H τ' * ψ H (sa * sb) := by
          rw [← map_mul, ← map_mul, eps_central τ' (mem_d8_iff.1 hτ'd)]
        calc x * ψ H (sa * sb) * x⁻¹ * ψ H τ
            = x * ψ H (sa * sb) * x⁻¹ * (x * ψ H τ' * x⁻¹) := by rw [← e1]
          _ = x * (ψ H (sa * sb) * ψ H τ') * x⁻¹ := by group
          _ = x * (ψ H τ' * ψ H (sa * sb)) * x⁻¹ := by rw [hcomm']
          _ = (x * ψ H τ' * x⁻¹) * (x * ψ H (sa * sb) * x⁻¹) := by group
          _ = ψ H τ * (x * ψ H (sa * sb) * x⁻¹) := by rw [← e1]
      rcases centre_d8 σ (mem_d8_iff.1 hσ) hσc with h3 | h3
      · exfalso
        have h4 : x * ψ H (sa * sb) * x⁻¹ = 1 := by rw [← hσa, h3, map_one]
        have ha1 : ψ H (sa * sb) = 1 := by
          have := congrArg (fun y => x⁻¹ * y * x) h4
          simpa [mul_assoc] using this
        exact eps_ne_one (hS.ψ_inj (by rw [ha1, map_one]))
      · have h4 : x * ψ H (sa * sb) * x⁻¹ = ψ H (sa * sb) := by rw [← hσa, h3]
        calc x * ψ H (sa * sb) = (x * ψ H (sa * sb) * x⁻¹) * x := by group
          _ = ψ H (sa * sb) * x := by rw [h4]
    have himg : ∀ v : V, ψ H (sa * sb) v * v⁻¹ ∈ fixV J := by
      intro v
      obtain ⟨w, hw, c, hc, rfl⟩ := hsplit H hH v
      have hac : ψ H (sa * sb) c = c := hc _ (hS.ψ_mem _)
      have e1 : ψ H (sa * sb) (w * c) * (w * c)⁻¹ = ψ H (sa * sb) w * w⁻¹ := by
        rw [map_mul, hac, mul_inv_rev]
        calc ψ H (sa * sb) w * c * (c⁻¹ * w⁻¹) = ψ H (sa * sb) w * w⁻¹ * (c * c⁻¹) := by ac_rfl
          _ = ψ H (sa * sb) w * w⁻¹ := by rw [mul_inv_cancel, mul_one]
      rw [e1]
      obtain ⟨y, rfl⟩ := hS.exists_β hw
      have e2 : ψ H (sa * sb) (β H y) * (β H y)⁻¹ = β H (coreAct 5 (sa * sb) y * y⁻¹) := by
        rw [map_mul (β H), map_inv (β H), hS.equiv]
      rw [e2]
      refine hfixJ _ fun H' hH' p hp => ?_
      by_cases hHH : H' = H
      · have hp' : p ∈ e4.map (ψ H) := hHH ▸ hp
        obtain ⟨τ, hτ, rfl⟩ := Subgroup.mem_map.1 hp'
        obtain ⟨hca, hcb⟩ := comm_eps_core y
        rw [← hS.equiv, fixed_of_e4 hca hcb τ hτ]
      · exact hfam.hother H hH H' hH' hHH p (hfam.map_le hH' _ hp) _ (hS.β_mem _)
    have hreg : ∀ v : V, ψ H (sa * sb) v = v → ∀ p ∈ e4.map (ψ H), p v = v := by
      intro v hav p hp
      obtain ⟨w, hw, c, hc, rfl⟩ := hsplit H hH v
      have hac : ψ H (sa * sb) c = c := hc _ (hS.ψ_mem _)
      have hpc : p c = c := hc p (hfam.map_le hH _ hp)
      rw [map_mul, hac] at hav
      have haw : ψ H (sa * sb) w = w := mul_right_cancel hav
      obtain ⟨y, rfl⟩ := hS.exists_β hw
      have hy : coreAct 5 (sa * sb) y = y := hS.β_inj (by rw [hS.equiv]; exact haw)
      obtain ⟨hya, hyb⟩ := fixed_eps_core y hy
      obtain ⟨τ, hτ, rfl⟩ := Subgroup.mem_map.1 hp
      rw [map_mul, hpc, ← hS.equiv, fixed_of_e4 hya hyb τ hτ]
    exact ⟨ψ H (sa * sb), hcommx, himg, hreg⟩
  choose! a ha using hblock
  exact fun v => trivial_of_commuting (Z := fixV J) hxcent (ι := ↥I) (fun h => a h.1)
    (fun h => (ha h.1 h.2).1) (fun h v => (ha h.1 h.2).2.1 v)
    (fun v hv => hfixJ v fun H hH p hp => (ha H hH).2.2 v (hv ⟨H, hH⟩) p hp) v

theorem centSub_eq : T ⊓ centSub (fixV (ffJP Ps T)) = ffJP Ps T := by
  have hJle : ffJP Ps T ≤ T := iSup_le fun _ => iSup_le fun _ => iSup_le fun hAT => hAT
  have hJc : ffJP Ps T ≤ centSub (fixV (ffJP Ps T)) := fun j hj z hz => hz j hj
  exact eq_of_trivial_action hD.ctx.hB.hV hD.ctx.hone (inf_le_left.trans hD.ctx.hmp.isSylow.1)
    (le_inf hJle hJc) hD.ffJP_ne_bot hD.card_le_J (fun x hx z hz => mem_centSub.1 hx.2 z hz)
    hD.trivial_action

end SymData

end Triv

end GE23

end CFSG.Quasithin
