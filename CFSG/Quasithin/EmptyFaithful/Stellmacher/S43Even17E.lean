module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43Even17D
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43EvenModS18

public section

namespace CFSG.Quasithin.F53.Stellmacher.S43.Even.E17

open CFSG.Quasithin.F53Mod Equiv

theorem case1_module (W : Model 5) (π : W.W →* orth.W) (hπs : Function.Surjective π)
    (hπe : ∀ (σ : Perm (Fin 5)) (w : W.W), π (W.act σ w) = orth.act σ (π w))
    (V : Subgroup W.W) (hVinj : ∀ v ∈ V, π v = 1 → v = 1)
    (hVY : V.map π = fixW orth S5That)
    (hVT : ∀ σ ∈ S5That, ∀ v ∈ V, W.act σ v = v)
    (hVS : ∀ σ ∈ S5Syl, ∀ v ∈ V, W.act σ v ∈ V)
    (hgen : ∀ U : Subgroup W.W, IsInvSub W ⊤ U → V ≤ U → U = ⊤)
    {t : Perm (Fin 5)} (ht : t.IsSwap) (ht4 : t 4 ≠ 4)
    (h6 : Nat.card (commW W (Subgroup.zpowers t) V) ≤ 2) (h7 : idx W t ≤ 4) :
    idx W t = 2 := by
  have ht1 : t ≠ 1 := by
    rintro rfl
    obtain ⟨a, b, hab, hs⟩ := ht
    have := congrArg (fun f => f a) hs
    simp only [Perm.coe_one, id_eq, swap_apply_left] at this
    exact hab this
  have hEb := isInvSub_ker hπe
  set R := W.restrict π.ker hEb with hR
  have hR2 := idx_restrict_ker_le hπs hπe ht h7
  obtain ⟨-, hcase⟩ := S11_model R ht1 hR2
  set A := alternatingGroup (Fin 5) with hAdef
  have hdich : (∃ π' : R.W →* orth.W, Function.Surjective π' ∧
      (∀ (σ : Perm (Fin 5)) (r : R.W), π' (R.act σ r) = orth.act σ (π' r)) ∧
      ∀ r : R.W, π' r = 1 → ∀ σ ∈ A, R.act σ r = r) ∨
      (∀ σ ∈ A, ∀ e ∈ π.ker, W.act σ e = e) := by
    rcases hcase with hc | ⟨hf, -, h2, -⟩
    · right
      intro σ hσ e he
      let r : R.W := W.restrictMk π.ker hEb e he
      have h1 : R.act σ r * r⁻¹ ∈ commW R A ⊤ :=
        Subgroup.subset_closure ⟨σ, hσ, r, Subgroup.mem_top _, rfl⟩
      rw [hc, Subgroup.mem_bot, mul_inv_eq_one] at h1
      exact congrArg Subtype.val h1
    · left
      have hK : IsInvSub R ⊤ (fixW R A) := isInvSub_fixW_of_normal R alternatingGroup.normal
      obtain ⟨-, -, ⟨e⟩⟩ := hss_1_5 R hf ht1 h2
      refine ⟨e.toMulEquiv.toMonoidHom.comp (R.projQuot _ hK), ?_, fun σ r => ?_, fun r hr => ?_⟩
      · exact e.toMulEquiv.surjective.comp (R.projQuot_surjective _ hK)
      · show e.toMulEquiv (R.projQuot _ hK (R.act σ r)) = orth.act σ (e.toMulEquiv
          (R.projQuot _ hK r))
        rw [← Model.projQuot_act, e.map_act]
      · have h1 : R.projQuot _ hK r = 1 := (MulEquiv.map_eq_one_iff e.toMulEquiv).mp hr
        have h2 : r ∈ (R.projQuot _ hK).ker := h1
        rw [Model.ker_projQuot] at h2
        exact h2
  have hdd : ∀ e ∈ π.ker, (∀ τ ∈ S5T, W.act τ e = e) → W.act dd e = e := by
    intro e he heT
    rcases hdich with ⟨π', -, hπ'e, hπ'k⟩ | hA5
    · let r : R.W := W.restrictMk π.ker hEb e he
      have hrT : ∀ τ ∈ S5T, R.act τ r = r := fun τ hτ => Subtype.ext (heT τ hτ)
      have h1 : orth.act dd (π' r) = π' r :=
        dd_fix_T fun τ hτ => by rw [← hπ'e, hrT τ hτ]
      have hc : π' (R.act dd r * r⁻¹) = 1 := by rw [map_mul, map_inv, hπ'e, h1, mul_inv_cancel]
      have hcfix := hπ'k _ hc dd dd_mem_alt
      have hrc : R.act dd r = (R.act dd r * r⁻¹) * r := by group
      have h2 := eq_one_of_cube dd_cube hrc hcfix
      rw [h2, one_mul] at hrc
      exact congrArg Subtype.val hrc
    · exact hA5 dd dd_mem_alt e he
  obtain ⟨u, hu, hπu⟩ := exists_S4_fixed W π hπe V hVY hVT hVS hdd
  obtain ⟨ι, hιe, hπι⟩ := exists_section W π hπe hu hπu
  let ρ : W.W →* W.W :=
    { toFun := fun w => w * (ι (π w))⁻¹
      map_one' := by simp
      map_mul' := fun a b => by
        simp only [map_mul, mul_inv]
        rw [mul_mul_mul_comm] }
  have hρ : ∀ w, ρ w = w * (ι (π w))⁻¹ := fun _ => rfl
  have hρK : ∀ w, π (ρ w) = 1 := fun w => by rw [hρ, map_mul, map_inv, hπι, mul_inv_cancel]
  have hρe : ∀ (σ : Perm (Fin 5)) (w : W.W), W.act σ (ρ w) = ρ (W.act σ w) := fun σ w => by
    rw [hρ, hρ, map_mul, map_inv, hιe, hπe]
  have hρι : ∀ o, ρ (ι o) = 1 := fun o => by rw [hρ, hπι, mul_inv_cancel]
  have hρw : ∀ w, ρ w * ι (π w) = w := fun w => by rw [hρ, inv_mul_cancel_right]
  have hρE : ∀ e ∈ π.ker, ρ e = e := fun e he => by
    rw [hρ, MonoidHom.mem_ker.mp he, map_one, inv_one, mul_one]
  obtain ⟨y₀, hy₀, hy₀1, hty₀⟩ := (swap_facts ht ht4).1
  obtain ⟨v₀, hv₀, hπv₀⟩ : y₀ ∈ V.map π := hVY ▸ hy₀
  have htv₀ := fix_of_card_le_two hπe hVS ht ht4 h6 hy₀ hy₀1 hty₀ hv₀ hπv₀
  have hVc := V_cases hπe hVinj hVY hVS ht ht4 hy₀ hy₀1 hty₀ hv₀ hπv₀
  have hidx2 : idx orth t = 2 := ((transvections t ht1).2).mpr ht
  rcases hdich with ⟨π', hπ's, hπ'e, -⟩ | hA5
  ·
    exfalso
    let ρ' : W.W →* R.W := ρ.codRestrict π.ker hρK
    have hρ' : ∀ w, Subtype.val (ρ' w) = ρ w := fun _ => rfl
    let Φ : W.W →* orth.W := π'.comp ρ'
    have hΦe : ∀ (σ : Perm (Fin 5)) (w : W.W), Φ (W.act σ w) = orth.act σ (Φ w) := by
      intro σ w
      have h1 : ρ' (W.act σ w) = R.act σ (ρ' w) := Subtype.ext (by
        rw [hρ', Model.restrict_act, hρ', hρe])
      show π' (ρ' (W.act σ w)) = orth.act σ (π' (ρ' w))
      rw [h1, hπ'e]
    have hΦs : ∀ o, ∃ w, Φ w = o := by
      intro o
      obtain ⟨r, hr⟩ := hπ's o
      refine ⟨Subtype.val r, ?_⟩
      have h1 : ρ' (Subtype.val r) = r := Subtype.ext (by rw [hρ', hρE _ r.2])
      show π' (ρ' (Subtype.val r)) = o
      rw [h1, hr]
    have hΦι : ∀ o, Φ (ι o) = 1 := by
      intro o
      have h1 : ρ' (ι o) = 1 := Subtype.ext (by rw [hρ', hρι]; rfl)
      show π' (ρ' (ι o)) = 1
      rw [h1, map_one]
    have hχ : ∀ χ : W.W →* orth.W, (∀ (σ : Perm (Fin 5)) (w : W.W),
        χ (W.act σ w) = orth.act σ (χ w)) → χ v₀ = 1 → ∀ w, χ w = 1 := by
      intro χ hχe hχ1 w
      have hker : χ.ker = ⊤ := by
        refine hgen χ.ker (isInvSub_ker hχe) fun v hv => ?_
        rw [MonoidHom.mem_ker]
        rcases hVc v hv with rfl | rfl | rfl | rfl
        · exact map_one χ
        · exact hχ1
        · rw [hχe, hχ1, map_one]
        · rw [map_mul, hχe, hχ1, map_one, one_mul]
      exact MonoidHom.mem_ker.mp (hker ▸ Subgroup.mem_top w)
    set a := Φ v₀ with ha
    have haT : a ∈ fixW orth S5That := fun σ hσ => by rw [ha, ← hΦe, hVT σ hσ v₀ hv₀]
    have hta : orth.act t a = a := by rw [ha, ← hΦe, htv₀]
    by_cases ha1 : a = 1
    · obtain ⟨w, hw⟩ := hΦs y₀
      rw [hχ Φ hΦe ha1 w] at hw
      exact hy₀1 hw.symm
    · have hay : a = y₀ := (swap_facts ht ht4).2.2.1 a haT y₀ hy₀ ha1 hy₀1 hta hty₀
      let χ : W.W →* orth.W :=
        { toFun := fun w => Φ w * (π w)⁻¹
          map_one' := by simp
          map_mul' := fun x y => by
            simp only [map_mul, mul_inv]
            rw [mul_mul_mul_comm] }
      have hχe : ∀ (σ : Perm (Fin 5)) (w : W.W), χ (W.act σ w) = orth.act σ (χ w) := by
        intro σ w
        show Φ (W.act σ w) * (π (W.act σ w))⁻¹ = orth.act σ (Φ w * (π w)⁻¹)
        rw [hΦe, hπe, map_mul, map_inv]
      have hχ1 : χ v₀ = 1 := by
        show Φ v₀ * (π v₀)⁻¹ = 1
        rw [← ha, hay, hπv₀, mul_inv_cancel]
      have h1 := hχ χ hχe hχ1 (ι y₀)
      have h2 : Φ (ι y₀) * (π (ι y₀))⁻¹ = 1 := h1
      rw [hΦι, hπι, one_mul, inv_eq_one] at h2
      exact hy₀1 h2
  ·
    have hU : (fixW W ⊤).comap ρ = ⊤ := by
      refine hgen _ (fun σ _ w hw => ?_) fun v hv => ?_
      · rw [Subgroup.mem_comap] at hw ⊢
        rw [← hρe]
        exact isInvSub_fixW_of_normal W Subgroup.normal_top σ (Subgroup.mem_top σ) _ hw
      · rw [Subgroup.mem_comap, mem_fixW]
        intro g _
        have hT : ∀ σ ∈ S5That, W.act σ (ρ v) = ρ v := fun σ hσ => by
          rw [hρe, hVT σ hσ v hv]
        have hAv : ∀ σ ∈ A, W.act σ (ρ v) = ρ v := fun σ hσ => hA5 σ hσ (ρ v) (hρK v)
        by_cases hg : Perm.sign g = 1
        · exact hAv g (Perm.mem_alternatingGroup.mpr hg)
        · have hs02 : swap (0 : Fin 5) 2 ∈ S5That := Subgroup.subset_closure (by simp)
          have hgA : g * swap 0 2 ∈ A := by
            rw [Perm.mem_alternatingGroup, map_mul, Perm.sign_swap (by decide)]
            rcases Int.units_eq_one_or (Perm.sign g) with h | h
            · exact absurd h hg
            · rw [h]; decide
          have e1 : g = (g * swap 0 2) * swap 0 2 := by rw [mul_assoc, swap_mul_self, mul_one]
          rw [e1, act_mul_apply, hT _ hs02, hAv _ hgA]
    have hρfix : ∀ w, ∀ σ : Perm (Fin 5), W.act σ (ρ w) = ρ w := fun w σ =>
      (show w ∈ (fixW W ⊤).comap ρ from hU ▸ Subgroup.mem_top w) σ (Subgroup.mem_top σ)
    have hle : (fixW orth (Subgroup.zpowers t)).comap π ≤ fixW W (Subgroup.zpowers t) := by
      intro w hw
      rw [Subgroup.mem_comap, mem_fixW_zpowers] at hw
      rw [mem_fixW_zpowers]
      calc W.act t w = W.act t (ρ w * ι (π w)) := by rw [hρw]
        _ = ρ w * ι (orth.act t (π w)) := by rw [map_mul, hρfix, hιe]
        _ = w := by rw [hw, hρw]
    have hle2 : idx W t ≤ 2 := by
      unfold idx
      calc (fixW W (Subgroup.zpowers t)).index ≤
            ((fixW orth (Subgroup.zpowers t)).comap π).index := Subgroup.index_antitone hle
        _ = (fixW orth (Subgroup.zpowers t)).index := Subgroup.index_comap_of_surjective _ hπs
        _ = 2 := hidx2
    have hne1 : idx W t ≠ 1 := by
      intro h1
      unfold idx at h1
      rw [Subgroup.index_eq_one] at h1
      have h3 : idx orth t = 1 := by
        unfold idx
        rw [Subgroup.index_eq_one, eq_top_iff]
        intro o _
        obtain ⟨w, rfl⟩ := hπs o
        rw [mem_fixW_zpowers, ← hπe, (mem_fixW_zpowers W).mp (h1 ▸ Subgroup.mem_top w)]
      omega
    have hpos : 0 < idx W t :=
      Nat.pos_of_ne_zero (by unfold idx; exact Subgroup.index_ne_zero_of_finite)
    omega

end CFSG.Quasithin.F53.Stellmacher.S43.Even.E17
