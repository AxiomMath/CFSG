module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps128Lift
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps128Bound

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo Subgroup
open scoped commutatorElement

theorem self_mem_conjSet {A : Type*} [Group A] (K N : Subgroup A) : K ∈ conjSet K N := by
  refine ⟨1, N.one_mem, ?_⟩
  ext x
  simp

theorem sup_mul_comm {G : Type*} [Group G] {A B D : Subgroup G}
    (hA : ∀ a ∈ A, ∀ d ∈ D, a * d = d * a) (hB : ∀ b ∈ B, ∀ d ∈ D, b * d = d * b) :
    ∀ x ∈ A ⊔ B, ∀ d ∈ D, x * d = d * x := by
  have hle : A ⊔ B ≤ Subgroup.centralizer (D : Set G) := by
    refine sup_le (fun a ha => ?_) (fun b hb => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro d hd
      exact (hA a ha d hd).symm
    · rw [Subgroup.mem_centralizer_iff]
      intro d hd
      exact (hB b hb d hd).symm
  intro x hx d hd
  exact (Subgroup.mem_centralizer_iff.mp (hle hx) d hd).symm

theorem map_conj_map_conj_of_mul_eq_one {W : Type} [CommGroup W] (K : Subgroup (MulAut W))
    {t : MulAut W} (ht2 : t * t = 1) :
    (K.map (MulAut.conj t).toMonoidHom).map (MulAut.conj t).toMonoidHom = K := by
  have e : ∀ y : MulAut W, t * (t * y * t⁻¹) * t⁻¹ = y := by
    intro y
    have e2 : t * (t * y * t⁻¹) * t⁻¹ = (t * t) * y * (t * t)⁻¹ := by group
    rw [e2, ht2, inv_one, one_mul, mul_one]
  rw [Subgroup.map_map]
  ext x
  simp only [Subgroup.mem_map, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
    MulAut.conj_apply, e, exists_eq_right]

variable {W : Type} [CommGroup W] [Finite W]

theorem commSub_le_of_ne_of_ne (hW : ∀ w : W, w ^ 2 = 1) {Y L H : Subgroup (MulAut W)}
    (hL : IsComponentOf L Y) (hH : H = ⨆ X ∈ conjSet L Y, X) {t : MulAut W} (ht : t ∈ Y)
    (ht2 : orderOf t = 2) (hm : rkIdx (fixV (Subgroup.zpowers t)) < dMinDeg ↥L)
    {U : Subgroup W} (hU : U ∈ irrSet H) (hUt : U.map t.toMonoidHom = U)
    (hLU : ¬ commSub U L ≤ fixV H) (htU : ¬ commSub U (Subgroup.zpowers t) ≤ fixV H)
    {K : Subgroup (MulAut W)} (hK : K ∈ conjSet L Y) (hKL : K ≠ L)
    (hKLt : K ≠ L.map (MulAut.conj t).toMonoidHom) : commSub U K ≤ fixV H := by
  by_contra hKU
  obtain ⟨-, hLH, hHY, hn, -, -⟩ := h_facts hL hH
  have hstab : Y ≤ stabSub (fixV H) := le_stabSub_fixV hn
  have hHstab : H ≤ stabSub (fixV H) := hHY.trans hstab
  have ht2' : t * t = 1 := by rw [← pow_two, ← ht2]; exact pow_orderOf_eq_one t
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2'
  obtain ⟨hKcomp, hKH, -⟩ := conjSet_facts hL hH hK
  have hLt : L.map (MulAut.conj t).toMonoidHom ∈ conjSet L Y := ⟨t, ht, rfl⟩
  obtain ⟨hLtcomp, hLtH, -⟩ := conjSet_facts hL hH hLt
  have hKt : K.map (MulAut.conj t).toMonoidHom ∈ conjSet L Y := by
    obtain ⟨n, hn', rfl⟩ := hK
    exact ⟨t * n, Y.mul_mem ht hn', CFSG.Quasithin.B19.map_conj_map_conj L _ _⟩
  obtain ⟨hKtcomp, hKtH, -⟩ := conjSet_facts hL hH hKt
  have hAK := sup_inf_trivMod_eq hL hH hU hK hKU
  have hAL := sup_inf_trivMod_eq hL hH hU (self_mem_conjSet L Y) hLU
  have hKle := le_commutator_sup_conj hKcomp ht ht2'
    (not_commute_of_not_commSub_le hW hL hH ht hm hU hUt htU hK hKU)
  have hKtL : K.map (MulAut.conj t).toMonoidHom ≠ L := by
    intro h
    apply hKLt
    rw [← h, map_conj_map_conj_of_mul_eq_one K ht2']
  have hKtLt : K.map (MulAut.conj t).toMonoidHom ≠ L.map (MulAut.conj t).toMonoidHom := by
    intro h
    apply hKL
    rw [← map_conj_map_conj_of_mul_eq_one K ht2', h, map_conj_map_conj_of_mul_eq_one L ht2']
  have hMB : ∀ m ∈ K ⊔ K.map (MulAut.conj t).toMonoidHom,
      ∀ b ∈ L ⊔ L.map (MulAut.conj t).toMonoidHom, m * b = b * m := by
    have h1 := B69.components_mul_comm_of_ne hL hKcomp (Ne.symm hKL)
    have h2 := B69.components_mul_comm_of_ne hLtcomp hKcomp (Ne.symm hKLt)
    have h3 := B69.components_mul_comm_of_ne hL hKtcomp (Ne.symm hKtL)
    have h4 := B69.components_mul_comm_of_ne hLtcomp hKtcomp (Ne.symm hKtLt)
    have hK' : ∀ k ∈ K, ∀ b ∈ L ⊔ L.map (MulAut.conj t).toMonoidHom, k * b = b * k := by
      intro k hk b hb
      exact (sup_mul_comm (fun l hl k hk => (h1 k hk l hl).symm)
        (fun l hl k hk => (h2 k hk l hl).symm) b hb k hk).symm
    have hKt' : ∀ k ∈ K.map (MulAut.conj t).toMonoidHom,
        ∀ b ∈ L ⊔ L.map (MulAut.conj t).toMonoidHom, k * b = b * k := by
      intro k hk b hb
      exact (sup_mul_comm (fun l hl k hk => (h3 k hk l hl).symm)
        (fun l hl k hk => (h4 k hk l hl).symm) b hb k hk).symm
    exact sup_mul_comm hK' hKt'
  set C := fixV H with hC
  set B₀ := L ⊔ L.map (MulAut.conj t).toMonoidHom with hB₀
  set M := K ⊔ K.map (MulAut.conj t).toMonoidHom with hM
  have hB₀H : B₀ ≤ H := sup_le hLH hLtH
  have hMH : M ≤ H := sup_le hKH hKtH
  have hV : ∀ v : W ⧸ C, v ^ 2 = 1 := by
    intro v
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective C v
    rw [← map_pow, hW, map_one]
  set U' := U.map (QuotientGroup.mk' C) with hU'
  set B' := autQuot B₀ C with hB'
  have hU's := map_mk_stable_irr hHstab hU
  have hU'H : autQuot H C ≤ stabSub U' := B1.le_stabSub_of_invariant hU's.1
  have hU'ne : U' ≠ ⊥ := by
    intro h
    apply not_le_fixV_of_mem_irrSet hU
    have h2 : U ≤ (QuotientGroup.mk' C).ker := by
      rw [← Subgroup.map_eq_bot_iff, ← hU', h]
    rwa [QuotientGroup.ker_mk'] at h2
  have hB'U' : StableUnder B' U' := fun φ hφ => hU's.1 φ (autQuot_mono hB₀H C hφ)
  have hU'0 : U' ⊓ fixV B' = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨u, hu, rfl⟩, hv⟩
    have hu' : u ∈ (U ⊔ C) ⊓ trivMod L C := by
      refine ⟨le_sup_left (α := Subgroup W) hu, fun l hl => ?_⟩
      have h1 := hv (quotHom C ⟨l, hHstab (hLH hl)⟩)
        (mem_autQuot.mpr ⟨_, le_sup_left (α := Subgroup (MulAut W)) hl, rfl⟩)
      rw [QuotientGroup.mk'_apply, quotHom_mk] at h1
      exact (mk_eq_mk_iff _ _).mp h1
    rw [hAL] at hu'
    rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hu'
  have hdL : ∀ {X : Subgroup (MulAut W)}, X ≤ H → (X = L ∨ X = L.map (MulAut.conj t).toMonoidHom) →
      ∀ J : Subgroup (W ⧸ C), StableUnder (autQuot X C) J → ¬ J ≤ fixV (autQuot X C) →
        dMinDeg ↥L ≤ rk ↥J := by
    intro X hXH hX J hJs hJX
    have h1 := dMinDeg_le_rk_of_not_le_fixV hV hJs hJX
    have hne : autQuot X C ≠ ⊥ := by
      intro h
      apply hJX
      rw [h]
      intro u _ φ hφ
      rw [Subgroup.mem_bot] at hφ
      rw [hφ]
      rfl
    have h2 := dMinDeg_le_autQuot (hXH.trans hHstab) hne
    have h3 : dMinDeg ↥X = dMinDeg ↥L := by
      rcases hX with rfl | rfl
      · rfl
      · exact (dMinDeg_congr (L.equivMapOfInjective _ (MulAut.conj t).injective)).symm
    omega
  have hrkJ : ∀ J ∈ minStab B' U', dMinDeg ↥L ≤ rk ↥J := by
    intro J hJ
    obtain ⟨hJU, hJs, hJne, -⟩ := hJ
    have hJ0 : ¬ J ≤ fixV B' := by
      intro hle
      apply hJne
      rw [eq_bot_iff, ← hU'0]
      exact le_inf hJU hle
    by_cases hLJ : J ≤ fixV (autQuot L C)
    · by_cases hLtJ : J ≤ fixV (autQuot (L.map (MulAut.conj t).toMonoidHom) C)
      · exfalso
        apply hJ0
        have hle : autQuot B₀ C ≤ centSub J := by
          rw [autQuot_le_iff (hB₀H.trans hHstab)]
          refine sup_le ?_ ?_
          · rw [← autQuot_le_iff (hLH.trans hHstab)]
            intro φ hφ u hu
            exact hLJ hu φ hφ
          · rw [← autQuot_le_iff (hLtH.trans hHstab)]
            intro φ hφ u hu
            exact hLtJ hu φ hφ
        intro u hu φ hφ
        exact hle hφ u hu
      · exact hdL hLtH (Or.inr rfl) J
          (fun φ hφ => hJs φ (autQuot_mono le_sup_right C hφ)) hLtJ
    · exact hdL hLH (Or.inl rfl) J (fun φ hφ => hJs φ (autQuot_mono le_sup_left C hφ)) hLJ
  have hB₀t : ∀ g ∈ B₀, t⁻¹ * g * t ∈ B₀ := by
    have hle : B₀ ≤ B₀.comap (MulAut.conj t⁻¹).toMonoidHom := by
      refine sup_le (fun l hl => ?_) ?_
      · rw [Subgroup.mem_comap]
        refine le_sup_right (α := Subgroup (MulAut W)) ⟨l, hl, ?_⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, htinv]
      · rintro _ ⟨l, hl, rfl⟩
        rw [Subgroup.mem_comap]
        refine le_sup_left (α := Subgroup (MulAut W)) ?_
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
        have e : t⁻¹ * (t * l * t⁻¹) * t = l := by group
        rw [e]
        exact hl
    intro g hg
    have h1 := hle hg
    rw [Subgroup.mem_comap] at h1
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using h1
  set τ := quotHom C ⟨t, hstab ht⟩ with hτ
  have hτB : ∀ b ∈ B', τ⁻¹ * b * τ ∈ B' := by
    intro b hb
    obtain ⟨g, hg, rfl⟩ := mem_autQuot.mp hb
    have e : τ⁻¹ * quotHom C g * τ =
        quotHom C ((⟨t, hstab ht⟩ : stabSub C)⁻¹ * g * ⟨t, hstab ht⟩) := by
      rw [hτ, map_mul, map_mul, map_inv]
    rw [e]
    exact mem_autQuot.mpr ⟨_, hB₀t g.1 hg, rfl⟩
  have hτJ : ∀ J ∈ minStab B' U', τ ∈ stabSub J := fun J hJ =>
    mem_stabSub_of_rkIdx_lt hτB hJ
      (lt_of_le_of_lt (rkIdx_fixV_quotHom_le (hstab ht)) (hm.trans_le (hrkJ J hJ)))
  have hperm : ∀ m ∈ M, ∀ hmC : m ∈ stabSub C, ∀ J ∈ minStab B' U',
      J.map (quotHom C ⟨m, hmC⟩).toMonoidHom ∈ minStab B' U' := by
    intro m hm hmC J hJ
    refine map_mem_minStab ?_ (hU'H (mem_autQuot.mpr ⟨_, hMH hm, rfl⟩)) hJ
    intro b hb
    exact autQuot_commute (X := M) (X' := B₀) hMB _ (mem_autQuot.mpr ⟨_, hm, rfl⟩) b hb
  set S : Subgroup (MulAut (W ⧸ C)) := ⨅ J ∈ minStab B' U', stabSub J with hS
  have hτS : Subgroup.zpowers τ ≤ S := by
    rw [Subgroup.zpowers_le, hS, Subgroup.mem_iInf]
    intro J
    rw [Subgroup.mem_iInf]
    exact hτJ J
  have hcomm_le : ⁅M, Subgroup.zpowers t⁆ ≤ liftSub C S := by
    rw [Subgroup.commutator_le]
    intro m hm s hs
    have hmC : m ∈ stabSub C := hHstab (hMH hm)
    have hsC : s ∈ stabSub C := (Subgroup.zpowers_le.mpr (hstab ht)) hs
    have hsτ : quotHom C ⟨s, hsC⟩ ∈ Subgroup.zpowers τ := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
      refine ⟨k, ?_⟩
      simp only [hτ]
      rw [← map_zpow]
      congr 1
    have hx : (⁅(⟨m, hmC⟩ : stabSub C), ⟨s, hsC⟩⁆ : stabSub C) ∈ S.comap (quotHom C) := by
      rw [Subgroup.mem_comap, map_commutatorElement, hS, Subgroup.mem_iInf]
      intro J
      rw [Subgroup.mem_iInf]
      intro hJ
      refine commutatorElement_mem_stabSub (𝒥 := minStab B' U') ?_ ?_ J hJ
      · intro J' hJ'
        have e : (quotHom C ⟨m, hmC⟩)⁻¹ = quotHom C ⟨m⁻¹, (stabSub C).inv_mem hmC⟩ := by
          rw [← map_inv]
          rfl
        rw [e]
        exact hperm _ (M.inv_mem hm) _ J' hJ'
      · intro J' hJ'
        have h1 := hτS hsτ
        rw [hS, Subgroup.mem_iInf] at h1
        exact (Subgroup.mem_iInf.mp (h1 J')) hJ'
    exact ⟨_, hx, rfl⟩
  have hKS : autQuot K C ≤ S :=
    (autQuot_le_iff (hKH.trans hHstab)).mpr (hKle.trans hcomm_le)
  obtain ⟨J₀, hJ₀⟩ := exists_mem_minStab hB'U' hU'ne
  have hJ₀0 : J₀ ⊓ fixV B' = ⊥ :=
    eq_bot_iff.mpr ((inf_le_inf_right _ hJ₀.1).trans hU'0.le)
  have hKst : K ≤ stabSub C := hKH.trans hHstab
  have hKperf : Group.IsPerfect ↥(autQuot K C) := by
    have : Group.IsPerfect ↥K := ⟨hKcomp.2.2.1⟩
    exact Group.IsPerfect.ofSurjective (f := ((quotHom C).subgroupMap
        (K.subgroupOf (stabSub C))).comp (Subgroup.subgroupOfEquivOfLe hKst).symm.toMonoidHom)
      (((quotHom C).subgroupMap_surjective _).comp
        (Subgroup.subgroupOfEquivOfLe hKst).symm.surjective)
  have hKB : ∀ k ∈ autQuot K C, ∀ b ∈ B', k * b = b * k :=
    autQuot_commute (fun k hk b hb => hMB k (le_sup_left (α := Subgroup (MulAut W)) hk) b hb)
  have hKJ : ∀ k ∈ autQuot K C, ∀ w ∈ J₀, k w ∈ J₀ := by
    intro k hk w hw
    have h1 := hKS hk
    rw [hS, Subgroup.mem_iInf] at h1
    exact ((Subgroup.mem_iInf.mp (h1 J₀) hJ₀) w).mpr hw
  have htriv := B69.trivial_of_perfect_commute hV (mem_irrPlus_of_mem_minStab hJ₀ hJ₀0)
    hKperf hKB hKJ
  obtain ⟨v, hv1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hJ₀.2.2.1
  obtain ⟨u, hu, hvu⟩ := hJ₀.1 v.2
  have hu' : u ∈ (U ⊔ C) ⊓ trivMod K C := by
    refine ⟨le_sup_left (α := Subgroup W) hu, fun k hk => ?_⟩
    have h1 := htriv (quotHom C ⟨k, hKst hk⟩) (mem_autQuot.mpr ⟨_, hk, rfl⟩) v v.2
    rw [← hvu, QuotientGroup.mk'_apply, quotHom_mk] at h1
    exact (mk_eq_mk_iff _ _).mp h1
  rw [hAK] at hu'
  apply hv1
  apply Subtype.ext
  rw [← hvu, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff u).mpr hu']
  rfl

end CFSG.LocalAnalysis.WeakClosure81
