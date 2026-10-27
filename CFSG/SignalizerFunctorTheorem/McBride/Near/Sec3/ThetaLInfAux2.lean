module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Lemma212Setup
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Lemma214
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm211Aux

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Thm33h

variable {Γ : Type*} [Group Γ] [Finite Γ] {p : ℕ} {A G W J : Subgroup Γ} {a : Γ}

theorem cenIn_le_of_not_centralizes
    (hss : SemisimpleAction p A G) (hJ : J ∈ lcal G)
    (haN : a ∈ norIn A J) (haC : a ∉ Subgroup.centralizer (J : Set Γ)) :
    cenIn J ({a} : Set Γ) ≤ cenIn J ((norIn A J : Subgroup Γ) : Set Γ) := by
  obtain ⟨a₀, f, ha₀, hf, hord, hpow, hfix⟩ := hss.exists_frame hJ
  obtain ⟨k, hk⟩ := hpow a haN
  have hpk : ¬ p ∣ k := by
    intro hpk
    have hf1 : f ^ k = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, hord]
      exact hpk
    apply haC
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 := hk ⟨x, hx⟩
    rw [hf1, MulAut.one_apply] at h1
    have h2 : a * x * a⁻¹ = x := h1
    rw [mul_inv_eq_iff_eq_mul] at h2
    exact h2.symm
  intro x hx
  obtain ⟨hxJ, hxa⟩ := Subgroup.mem_inf.1 hx
  refine Subgroup.mem_inf.2 ⟨hxJ, Subgroup.mem_centralizer_iff.2 fun n hn => ?_⟩
  obtain ⟨m, hm⟩ := hpow n hn
  have hax : a * x * a⁻¹ = x := by
    rw [mul_inv_eq_iff_eq_mul]
    exact (Subgroup.mem_centralizer_singleton_iff.1 hxa).symm
  have h1 : (f ^ k) ⟨x, hxJ⟩ = ⟨x, hxJ⟩ := Subtype.ext ((hk ⟨x, hxJ⟩).symm.trans hax)
  have h2 : f ⟨x, hxJ⟩ = ⟨x, hxJ⟩ :=
    Lemma214.apply_eq_of_pow_apply_eq hss.prime hord hpk h1
  have h3 : (f ^ m) ⟨x, hxJ⟩ = ⟨x, hxJ⟩ := Lemma214.pow_apply_eq_of_apply_eq h2 m
  have h4 := hm ⟨x, hxJ⟩
  rw [h3] at h4
  have h5 : n * x * n⁻¹ = x := h4
  rw [mul_inv_eq_iff_eq_mul] at h5
  exact h5

theorem eq_bot_of_normalized
    (H : Lemma212.Hyp p A G) (ha : a ∈ A) (ha1 : a ≠ 1)
    (hWK : W ≤ cenIn (kOf G) ({a} : Set Γ))
    (hWadm : Admits (A ⊔ cenIn (kOf G) ({a} : Set Γ)) W)
    (hWsol : Group.IsSolvable ↥W) (hWA : cenIn W (A : Set Γ) = ⊥) : W = ⊥ := by
  have hss := H.semisimpleAction
  by_cases hsolv : Group.IsSolvable ↥(cenIn (kOf G) ({a} : Set Γ))
  · exact lemma214 hss.toNearAction hss.semisimple ha ha1 hsolv hWK hWadm hWA
  have hX : IsDirectProduct (lcal (kOf G)) (kOf G) := hss.isDirectProduct_lcal
  have hperm : ∀ b ∈ Subgroup.zpowers a, ∀ J ∈ lcal (kOf G),
      J.map (MulAut.conj b).toMonoidHom ∈ lcal (kOf G) := fun b hb J hJ =>
    map_conj_mem_lcal hJ (hss.admits (Subgroup.zpowers_le.2 ha hb))
  have hcenK : kOf G ⊓ Subgroup.centralizer ((Subgroup.zpowers a : Subgroup Γ) : Set Γ) =
      cenIn (kOf G) ({a} : Set Γ) := by
    unfold cenIn
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hcenJ : ∀ J : Subgroup Γ, J ⊓ Subgroup.centralizer
      ((Subgroup.zpowers a : Subgroup Γ) : Set Γ) = cenIn J ({a} : Set Γ) := by
    intro J
    unfold cenIn
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hnotI : ∀ J ∈ lcal (kOf G), ¬ (a ∈ Subgroup.normalizer (J : Set Γ) ∧
      a ∉ Subgroup.centralizer (J : Set Γ)) := by
    rintro J₀ hJ₀ ⟨hN₀, hC₀⟩
    apply hsolv
    refine Thm210.isSolvable_of_forall_projIn hX inf_le_left fun J hJ => ?_
    have hJ₀' : J₀ ∈ lcal G := H.lcal_kOf ▸ hJ₀
    have hJ' : J ∈ lcal G := H.lcal_kOf ▸ hJ
    have hN : a ∈ Subgroup.normalizer (J : Set Γ) := (H.norm_iff hJ₀' hJ' ha).mpr hN₀
    have hC : a ∉ Subgroup.centralizer (J : Set Γ) := fun hc =>
      hC₀ ((H.cent_iff hJ₀' hJ' ha).mp hc)
    have hproj := projIn_centralizer_eq hX hperm hJ
    rw [hcenK, inf_eq_left.mpr (Subgroup.zpowers_le.2 hN), hcenJ] at hproj
    rw [hproj]
    exact Thm211.isSolvable_of_le
      (cenIn_le_of_not_centralizes hss hJ ⟨ha, hN⟩ hC) (hss.isSolvable_cenIn_norIn hJ)
  have hWK' : W ≤ kOf G := hWK.trans inf_le_left
  have hall : ∀ J ∈ lcal (kOf G), projIn (lcal (kOf G)) J W = ⊥ := by
    intro J hJ
    have hproj := projIn_centralizer_eq hX hperm hJ
    rw [hcenK] at hproj
    have hJproj : projIn (lcal (kOf G)) J (cenIn (kOf G) ({a} : Set Γ)) = J := by
      rw [hproj]
      by_cases hN : a ∈ Subgroup.normalizer (J : Set Γ)
      · have hC : a ∈ Subgroup.centralizer (J : Set Γ) :=
          by_contra fun hC => hnotI J hJ ⟨hN, hC⟩
        refine inf_eq_left.mpr fun x hx => ?_
        refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
        have hyz : y ∈ Subgroup.zpowers a := (Subgroup.mem_inf.1 hy).1
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hyz
        have hCn : ∀ n : ℤ, a ^ n ∈ Subgroup.centralizer (J : Set Γ) := fun n =>
          zpow_mem hC n
        have := Subgroup.mem_centralizer_iff.1 (hCn n) x hx
        exact this.symm
      · have hbot : Subgroup.zpowers a ⊓ Subgroup.normalizer (J : Set Γ) = ⊥ := by
          rw [eq_bot_iff]
          intro b hb
          obtain ⟨hbz, hbN⟩ := Subgroup.mem_inf.1 hb
          rw [Subgroup.mem_bot]
          by_contra hb1
          exact hN ((Subgroup.zpowers_le.2 hbN)
            (Lemma214.mem_zpowers_of_mem_zpowers hss.prime (hss.elemAbelian.2 a ha) ha1 hbz hb1))
        rw [hbot, Thm211.centralizer_bot, inf_top_eq]
    have hQJ : projIn (lcal (kOf G)) J W ≤ J := projIn_le J W
    have hconj : ∀ y ∈ cenIn (kOf G) ({a} : Set Γ), ∀ w ∈ W, y * w * y⁻¹ ∈ W :=
      fun y hy w hw => (Subgroup.mem_normalizer_iff.1 (hWadm (Subgroup.mem_sup_right hy)) w).1 hw
    have hnorm : J ≤ Subgroup.normalizer ((projIn (lcal (kOf G)) J W : Subgroup Γ) : Set Γ) := by
      refine Thm210.le_normalizer_of_conj_mem fun c hc z hz => ?_
      have hc' : c ∈ projIn (lcal (kOf G)) J (cenIn (kOf G) ({a} : Set Γ)) := by
        rw [hJproj]
        exact hc
      exact Thm210.projIn_conj_mem hX hJ hconj c hc' z hz
    have hQsol : Group.IsSolvable ↥(projIn (lcal (kOf G)) J W) :=
      Thm210.isSolvable_projIn hX hJ hWK' hWsol
    obtain ⟨-, -, hsimple, -⟩ := mem_lcal_iff.1 hJ
    have hnormal : ((projIn (lcal (kOf G)) J W).subgroupOf J).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hQJ).2 hnorm
    have := hsimple
    have := hnormal
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ((projIn (lcal (kOf G)) J W).subgroupOf J) with hbot | htop
    · rw [← Subgroup.map_subgroupOf_eq_of_le hQJ, hbot, Subgroup.map_bot]
    · exfalso
      have hJQ : J ≤ projIn (lcal (kOf G)) J W := Subgroup.subgroupOf_eq_top.1 htop
      exact not_isSolvable_of_mem_lcal hJ (Thm211.isSolvable_of_le hJQ hQsol)
  rw [eq_bot_iff]
  intro w hw
  have hwK : w ∈ kOf G := hWK' hw
  have h1 : (⟨w, hwK⟩ : ↥(kOf G)) = 1 := by
    refine hX.ext_coord fun J hJ => ?_
    rw [map_one]
    have hmem : ((hX.coord hJ ⟨w, hwK⟩ : J) : Γ) ∈ projIn (lcal (kOf G)) J W :=
      (hX.mem_projIn_iff hJ).2 ⟨⟨w, hwK⟩, hw, rfl⟩
    rw [hall J hJ, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  exact Subgroup.mem_bot.2 (congrArg Subtype.val h1)

end CFSG.SignalizerFunctorTheorem.McBride.Near.Thm33h
