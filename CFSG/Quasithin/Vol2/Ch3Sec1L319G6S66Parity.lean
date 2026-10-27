module

public import CFSG.Quasithin.Vol2.Ch3Sec1L319Good

public section

namespace CFSG.Quasithin.H13.L319.S66

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.Ch3z

private theorem allBlocks_not_isPerfect_of_perm {K : Type} [Group K] {m : ℕ} (hm : 2 ≤ m)
    (θ : K ≃* Equiv.Perm (Fin m)) : ¬ Group.IsPerfect K := by
  intro hK
  have hPerm : Group.IsPerfect (Equiv.Perm (Fin m)) :=
    Group.IsPerfect.ofSurjective (f := θ.toMonoidHom) θ.surjective
  have hsign : Function.Surjective (Equiv.Perm.sign : Equiv.Perm (Fin m) →* ℤˣ) := by
    intro u
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact ⟨1, map_one _⟩
    · have hne : (⟨0, by omega⟩ : Fin m) ≠ ⟨1, by omega⟩ := by
        intro h
        have := congrArg Fin.val h
        simp at this
      exact ⟨Equiv.swap _ _, Equiv.Perm.sign_swap hne⟩
  have hZ : Group.IsPerfect ℤˣ := Group.IsPerfect.ofSurjective hsign
  haveI : IsMulCommutative ℤˣ := ⟨⟨fun a b => mul_comm a b⟩⟩
  have h1 : (-1 : ℤˣ) = 1 := Subsingleton.elim _ _
  have h2 := congrArg (fun u : ℤˣ => (u : ℤ)) h1
  norm_num at h2

theorem allBlocks_natural_of_step {G : Type} [Group G] [Finite G] {H T M₂ U A L N L' N' : Subgroup G}
    (hB1 : B69One) (h : Ch3z.Setting H T M₂ U A)
    (hstep : IsChiefStep H U L N) (hnc : ¬ IsCentralStep H L N)
    (hstep' : IsChiefStep H U L' N') (hnc' : ¬ IsCentralStep H L' N')
    (hJ : centralizerMod L' H N' = centralizerMod L H N)
    {𝓗 : Finset (Subgroup (MulAut ↥(chiefMod L N)))}
    (hctx : @Ch3z.BlkCtx ↥(chiefMod L N) (chiefCG (h.hE hstep)) (chiefAut H L N)
        (chiefImg (Setting.hHL hstep) (Setting.hHN hstep) T)
        (chiefImg (Setting.hHL hstep) (Setting.hHN hstep) M₂) 𝓗)
    {H' : Subgroup (MulAut ↥(chiefMod L N))} (hH' : H' ∈ 𝓗)
    (hNat : @Ch3z.NatBlockData ↥(chiefMod L N) (chiefCG (h.hE hstep)) H'
        (@CFSG.Quasithin.commV ↥(chiefMod L N) (chiefCG (h.hE hstep)) H') 2)
    {𝓗' : Finset (Subgroup (MulAut ↥(chiefMod L' N')))}
    (hctx' : @Ch3z.BlkCtx ↥(chiefMod L' N') (chiefCG (h.hE hstep')) (chiefAut H L' N')
        (chiefImg (Setting.hHL hstep') (Setting.hHN hstep') T)
        (chiefImg (Setting.hHL hstep') (Setting.hHN hstep') M₂) 𝓗') :
    ∀ K ∈ 𝓗', ∃ e : ℕ, 2 ≤ e ∧
      @Ch3z.NatBlockData ↥(chiefMod L' N') (chiefCG (h.hE hstep')) K
        (@CFSG.Quasithin.commV ↥(chiefMod L' N') (chiefCG (h.hE hstep')) K) e := by
  let _ : CommGroup ↥(chiefMod L N) := chiefCG (h.hE hstep)
  let _ : CommGroup ↥(chiefMod L' N') := chiefCG (h.hE hstep')
  have hA : ∃ K₁ ∈ 𝓗', ∃ e : ℕ, 2 ≤ e ∧
      @Ch3z.NatBlockData ↥(chiefMod L' N') (chiefCG (h.hE hstep')) K₁
        (@CFSG.Quasithin.commV ↥(chiefMod L' N') (chiefCG (h.hE hstep')) K₁) e := by
    by_contra hall
    have hsym : ∀ K ∈ 𝓗', ∃ m, @SymBlk ↥(chiefMod L' N') (chiefCG (h.hE hstep'))
        (chiefImg (Setting.hHL hstep') (Setting.hHN hstep') M₂) K m := by
      intro K hK
      rcases hctx'.symBlk_or_bad hK with hs | ⟨e, he, hN, -⟩
      · exact hs
      · exact (hall ⟨K, hK, e, he, hN⟩).elim
    obtain ⟨χ₀, hχC', a, haA, ha, hχa⟩ := chiefGood_of_symBlk hB1 h hstep' hnc' hctx' hsym
    have hχC : ∀ g : ↥H, (g : G) ∈ centralizerMod L H N → χ₀ g = 1 := by
      intro g hg
      apply hχC' g
      rw [hJ]
      exact hg
    obtain ⟨χ, hχ⟩ := CFSG.Quasithin.Ch3z.exists_factor (Setting.hHL hstep) (Setting.hHN hstep)
      (h.hNL hstep) χ₀ hχC
    have hstrong := h.noStrong hB1 hstep hnc
    obtain ⟨hAe, hA1, hoff⟩ := h.offender hstep hnc
    have hAJ := CFSG.Quasithin.Ch3z.le_ffJ_of_offender hstrong
      (CFSG.Quasithin.Ch3z.chiefImg_le_chiefAut (Setting.hHL hstep) (Setting.hHN hstep) A) hAe hA1 hoff
    have hmemA : CFSG.Quasithin.Ch3z.chiefPsi (Setting.hHL hstep) (Setting.hHN hstep) ⟨a, ha⟩ ∈
        CFSG.Quasithin.Ch3z.chiefImg (Setting.hHL hstep) (Setting.hHN hstep) A :=
      ⟨⟨a, ha⟩, Subgroup.mem_subgroupOf.mpr haA, rfl⟩
    have h1 := hctx.kills_of_bad hH' (le_refl (2 : ℕ)) hNat χ _ (hAJ hmemA)
      (CFSG.Quasithin.Ch3z.chiefPsi_mem (Setting.hHL hstep) (Setting.hHN hstep) ⟨a, ha⟩)
    have h2 : χ (CFSG.Quasithin.Ch3z.chiefHom (Setting.hHL hstep) (Setting.hHN hstep) ⟨a, ha⟩) = -1 := by
      rw [hχ]
      exact hχa
    have h3 : (1 : ℤˣ) = -1 := h1.symm.trans h2
    exact absurd h3 (by decide)
  obtain ⟨K₁, hK₁, e₁, he₁, hN₁⟩ := hA
  have hperf₁ : Group.IsPerfect ↥K₁ := hN₁.isPerfect he₁
  intro K hK
  rcases hctx'.symBlk_or_bad hK with ⟨m, hm⟩ | ⟨e, he, hN, -⟩
  · exfalso
    obtain ⟨t, -, hc⟩ := hctx'.trans hK₁ hK
    have hmap : B6.conjSub t K₁ = K₁.map (MulAut.conj t).toMonoidHom := rfl
    have hperfK : Group.IsPerfect ↥K := by
      rw [← hc, hmap]
      exact Group.IsPerfect.map (MulAut.conj t).toMonoidHom
    obtain ⟨hm3, -, θ, -⟩ := hm
    exact allBlocks_not_isPerfect_of_perm (by omega) θ hperfK
  · exact ⟨e, he, hN⟩

end CFSG.Quasithin.H13.L319.S66

end
