module

public import CFSG.Quasithin.Vol2.GoldschmidtF431UnStd
public import CFSG.Quasithin.Vol2.GoldschmidtF431TSLocK
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnLocDatum

public section

namespace CFSG.Quasithin.H13.F431.Un

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin.H13.F431.Lift
open scoped commutatorElement

section Lift

variable {D C : Type} [Group D] [Group C] (A : LieAmalgamExt D)
  (hgen : (MulAut.conj : D →* MulAut D).range ≤ A.K) (ε : D ≃* C)

@[expose] noncomputable def lamK : C →* ↥A.K := (iK A hgen).comp ε.symm.toMonoidHom

variable {A hgen ε}

theorem lamK_apply (c : C) : lamK A hgen ε c = iK A hgen (ε.symm c) := rfl

theorem lamK_injective (hcen : Subgroup.center D = ⊥) :
    Function.Injective (lamK A hgen ε) := (iK_injective A hgen hcen).comp ε.symm.injective

theorem lamK_conj (k : ↥A.K) (c : C) :
    k * lamK A hgen ε c * k⁻¹ = lamK A hgen ε (MulAut.congr ε (k : MulAut D) c) := by
  rw [lamK_apply, lamK_apply, conj_iK A hgen k]
  simp [MulAut.congr_apply]

theorem lamK_mem_centralizer_iff (hcen : Subgroup.center D = ⊥) (t : C) (k : ↥A.K) :
    k ∈ Subgroup.centralizer ({lamK A hgen ε t} : Set ↥A.K) ↔
      MulAut.congr ε (k : MulAut D) t = t := by
  have hc : ∀ c : C, MulAut.congr ε (k : MulAut D) c = ε ((k : MulAut D) (ε.symm c)) :=
    fun c => by simp [MulAut.congr_apply]
  rw [lamK_apply, mem_centralizer_iK_iff A hgen hcen, hc]
  constructor
  · intro h
    rw [h, MulEquiv.apply_symm_apply]
  · intro h
    have := congrArg ε.symm h
    simpa using this

theorem unLoc442Lie_of_std (hcen : Subgroup.center D = ⊥) {U : Subgroup C} {z t : C}
    {V Uc R K : Subgroup C} (S : UnStdLoc C U z t V Uc R K)
    (hU : A.TD.map ε.toMonoidHom = U) :
    UnLoc442Lie (A.TD.map (iK A hgen)) (lamK A hgen ε z) (lamK A hgen ε t)
      (V.map (lamK A hgen ε)) (Uc.map (lamK A hgen ε)) (R.map (lamK A hgen ε))
      (K.map (lamK A hgen ε)) := by
  set lam := lamK A hgen ε with hlam
  have hinj : Function.Injective lam := lamK_injective hcen
  have hcentK : ∀ x : C, x ∈ Subgroup.centralizer ({t} : Set C) →
      lam x ∈ Subgroup.centralizer ({lam t} : Set ↥A.K) := fun x hx => by
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    rw [← map_mul, ← map_mul, hx]
  have hfix : ∀ x ∈ Subgroup.centralizer ({lam t} : Set ↥A.K),
      MulAut.congr ε (x : MulAut D) t = t := fun x hx =>
    (lamK_mem_centralizer_iff hcen t x).1 hx
  have hmemU : ∀ {d : D}, d ∈ A.TD → ε d ∈ U := fun {d} hd => hU ▸ ⟨d, hd, rfl⟩
  have hcommD : ∀ {d : D} {c : C}, ε d * c = c * ε d → iK A hgen d * lam c = lam c * iK A hgen d :=
    fun {d c} h => by
      rw [hlam, lamK_apply, ← map_mul, ← map_mul]
      congr 1
      apply ε.injective
      simpa using h
  refine ⟨?_, ?_, ?_, ?_, ⟨z, S.z_V, rfl⟩, Subgroup.map_mono S.U_le, ?_, ⟨t, S.t_U, rfl⟩, ?_, ?_,
    Subgroup.map_mono S.V_K, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨v, hv, rfl⟩
    exact hcentK v (S.V_le hv)
  · rintro x hx _ ⟨v, hv, rfl⟩
    rw [lamK_conj]
    exact ⟨_, S.V_aut _ (hfix x hx) v hv, rfl⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, S.V_ab a ha b hb]
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, S.V_sq a ha, map_one]
  · rintro x hx _ ⟨u, hu, rfl⟩
    rw [lamK_conj]
    exact ⟨_, S.U_aut _ (hfix x hx) u hu, rfl⟩
  · rintro _ ⟨k, hk, rfl⟩
    exact hcentK k (S.K_le hk)
  · rw [← Subgroup.map_commutator, S.K_perf]
  · rintro _ ⟨k, hk, rfl⟩ _ ⟨u, hu, rfl⟩
    rw [← map_mul, ← map_mul, S.K_cent k hk u hu]
  · rintro _ ⟨v, hv, rfl⟩ hnu
    obtain ⟨x, hx, u, hu, h⟩ := S.coset v hv (fun h => hnu ⟨v, h, rfl⟩)
    refine ⟨lam x, hcentK x hx, lam u, ⟨u, hu, rfl⟩, ?_⟩
    rw [h]
    simp [map_mul, map_inv]
  · obtain ⟨L, hL, hLns, hLV⟩ := S.nonsolv
    refine ⟨L.map lam, ?_, ?_, ?_⟩
    · rintro _ ⟨l, hl, rfl⟩
      exact hcentK l (hL hl)
    · intro hsol
      have : Group.IsSolvable ↥(L.map lam) := hsol
      exact hLns (Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.equivMapOfInjective L lam hinj).toMonoidHom)
        (fun a b h => (Subgroup.equivMapOfInjective L lam hinj).injective h))
    · intro L' hL' hcond
      set L'' : Subgroup C := L'.comap lam with hL''
      have hL''L : L'' ≤ L := by
        intro x hx
        obtain ⟨y, hy, hyx⟩ := hL' hx
        exact hinj hyx ▸ hy
      have hL'eq : L''.map lam = L' :=
        Subgroup.map_comap_eq_self (fun x hx => (Subgroup.map_le_range lam L (hL' hx)))
      have : Group.IsSolvable ↥L'' := hLV L'' hL''L (fun x hx v hv => by
        have h1 := hcond (lam x) hx (lam v) ⟨v, hv, rfl⟩
        have h2 : lam (x * v * x⁻¹ * v⁻¹) ∈ Uc.map lam := by
          simpa [map_mul, map_inv] using h1
        exact (Subgroup.mem_map_iff_mem hinj).1 h2)
      have h3 : Group.IsSolvable ↥(L''.map lam) :=
        Group.isSolvable_of_isSolvable_injective
          (f := (Subgroup.equivMapOfInjective L'' lam hinj).symm.toMonoidHom)
          (fun a b h => (Subgroup.equivMapOfInjective L'' lam hinj).symm.injective h)
      rw [hL'eq] at h3
      exact h3
  · exact Subgroup.map_mono S.R_le
  · obtain ⟨a, ha, b, hb, ha1, hb1, hab⟩ := S.R_two
    exact ⟨lam a, ⟨a, ha, rfl⟩, lam b, ⟨b, hb, rfl⟩,
      fun h => ha1 (hinj (h.trans (map_one lam).symm)),
      fun h => hb1 (hinj (h.trans (map_one lam).symm)), fun h => hab (hinj h)⟩
  · rintro _ ⟨r, hr, rfl⟩ hr1
    obtain ⟨x, hx, hxr⟩ := S.R_cls r hr (fun h => hr1 (by rw [h, map_one]))
    refine ⟨lam x, hcentK x hx, ?_⟩
    rw [hxr]
    simp [map_mul, map_inv]
  · rintro _ ⟨r, hr, rfl⟩ hrU
    have : r ∈ Uc := (Subgroup.mem_map_iff_mem hinj).1 hrU
    rw [S.R_U r hr this, map_one]
  · rintro _ ⟨d, hd, rfl⟩
    exact hcommD ((S.z_cent (ε d) (hmemU hd)))
  · rintro _ ⟨⟨d, hd, rfl⟩, hy⟩ _ ⟨u, hu, rfl⟩
    have hdt : ε d ∈ Subgroup.centralizer ({t} : Set C) := by
      have hy' : iK A hgen d * lam t = lam t * iK A hgen d :=
        Subgroup.mem_centralizer_singleton_iff.1 hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      rw [hlam, lamK_apply, ← map_mul, ← map_mul] at hy'
      have := iK_injective A hgen hcen hy'
      have h2 := congrArg ε this
      simpa using h2
    exact hcommD (S.P_U (ε d) ⟨hmemU hd, hdt⟩ u hu)

end Lift

end CFSG.Quasithin.H13.F431.Un
