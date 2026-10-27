module

public import CFSG.Quasithin.Background.SmithB42HatA6Coord
public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitStmts
public import CFSG.Quasithin.Background.SmithB42Alt7Fix
public import CFSG.Quasithin.Background.B4ModelsAction

public section

namespace CFSG.Quasithin.HatA6

open CFSG.CharacterTheory.SteinbergBY
open scoped Matrix

variable {V : Type} [CommGroup V]

theorem quasisimple_card {X : Type*} [Group X] (hperf : Group.IsPerfect X)
    (hZ : Nat.card (Subgroup.center X) = 3)
    (e : X ⧸ Subgroup.center X ≃* alternatingGroup (Fin 6)) :
    CFSG.IsQuasisimple X ∧ Nat.card X = 1080 := by
  have hs6 : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  refine ⟨⟨hperf, e.isSimpleGroup, ?_⟩, ?_⟩
  · obtain ⟨a, b, hab⟩ := H13.alternatingGroup_nonabelian (n := 6) (by norm_num)
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    have := congrArg e h
    simpa using this
  · rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X),
      Nat.card_congr e.toEquiv, H13.card_alternatingGroup_fin 6 (by norm_num), hZ]
    decide

theorem exists_center_fpf [Finite V] (hsq2 : ∀ v : V, v ^ 2 = 1) (hV : Nat.card V = 2 ^ 6)
    {H : Subgroup (MulAut V)} (hperf : Group.IsPerfect ↥H) (hZ : Nat.card (Subgroup.center ↥H) = 3)
    (e : ↥H ⧸ Subgroup.center ↥H ≃* alternatingGroup (Fin 6)) :
    ∃ zH : ↥H, Subgroup.center ↥H = Subgroup.zpowers zH ∧ (zH : MulAut V) ^ 3 = 1 ∧
      ∀ v : V, (zH : MulAut V) v = v → v = 1 := by
  obtain ⟨hq, hH⟩ := quasisimple_card hperf hZ e
  have hZ1 : Subgroup.center ↥H ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hZ
    omega
  obtain ⟨⟨zH, hzc⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hZ1
  have hzH1 : zH ≠ 1 := fun h => hz1 (Subtype.ext h)
  have h3H : zH ^ 3 = 1 := by
    have h := pow_card_eq_one' (G := ↥(Subgroup.center ↥H)) (x := ⟨zH, hzc⟩)
    rw [hZ] at h
    exact congrArg Subtype.val h
  have h3 : (zH : MulAut V) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, h3H]
    rfl
  have hNfp : ∀ v ∈ H13.normKer (zH : MulAut V), (zH : MulAut V) v = v → v = 1 :=
    fun v hv hzv => H13.eq_one_of_mem_normKer hsq2 hv hzv
  have hN1 : H13.normKer (zH : MulAut V) ≠ ⊥ := by
    intro hbot
    apply hzH1
    apply Subtype.ext
    refine MulEquiv.ext fun v => ?_
    have hmem := H13.inv_mul_mem_normKer h3 v
    rw [hbot, Subgroup.mem_bot, inv_mul_eq_one] at hmem
    exact hmem.symm
  have hNtop := H13.eq_top_of_fpf hsq2 hV hq hZ hH hzc h3 (H13.normKer_invariant hzc) hN1 hNfp
  refine ⟨zH, ?_, h3, fun v hzv => hNfp v (hNtop ▸ Subgroup.mem_top v) hzv⟩
  have hle : Subgroup.zpowers zH ≤ Subgroup.center ↥H := Subgroup.zpowers_le.2 hzc
  have hord : orderOf zH = 3 := orderOf_eq_prime h3H hzH1
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [hZ, Nat.card_zpowers, hord]


section Model

variable {hsq : ∀ v : V, v * v = 1} {z : MulAut V} {u : Fin 3 → V}
  (hb : Function.Bijective (coordHom hsq z u)) (hzz : ∀ w, z (z w) = w * z w)
  {H : Subgroup (MulAut V)} (hH : ∀ x ∈ H, ∀ w, x (z w) = z (x w))

@[expose] noncomputable def gam : Subgroup (GL (Fin 3) FieldFour) := (glOf hb hzz H hH).range

@[expose] noncomputable def gamEquiv : ↥H ≃* ↥(gam hb hzz hH) :=
  MonoidHom.ofInjective (glOf_injective hb hzz H hH)

theorem coe_gamEquiv (h : ↥H) :
    ((gamEquiv hb hzz hH h : ↥(gam hb hzz hH)) : GL (Fin 3) FieldFour) = glOf hb hzz H hH h :=
  rfl

theorem linOf_eq_smul {x : MulAut V} (hx : ∀ w, x (z w) = z (x w)) (hxz : x = z) :
    linOf hb hzz hx = FieldFour.ω • LinearMap.id := by
  subst hxz
  exact linOf_z hb hzz hx

theorem glOf_eq_smul (h : ↥H) (hhz : (h : MulAut V) = z) :
    ((glOf hb hzz H hH h : GL (Fin 3) FieldFour) : Matrix (Fin 3) (Fin 3) FieldFour) =
      FieldFour.ω • 1 := by
  change matOf hb hzz _ = _
  rw [matOf, linOf_eq_smul hb hzz _ hhz, map_smul, LinearMap.toMatrix'_id]

theorem realizesVia_gam :
    (FFModel.nat (gam hb hzz hH)).RealizesVia H ⊤ ⊥ (gamEquiv hb hzz hH).symm.toMonoidHom := by
  refine B42Alt7.realizesVia_of_equivariant (FFModel.nat_isActionModel _) rfl H _
    (gamEquiv hb hzz hH).symm.surjective ((coordEquiv hb).symm.trans Subgroup.topEquiv.symm) ?_
  intro γ s
  obtain ⟨h, rfl⟩ := (gamEquiv hb hzz hH).surjective γ
  change (coordEquiv hb).symm
      ((((gamEquiv hb hzz hH).symm (gamEquiv hb hzz hH h) : ↥H) : MulAut V) s) =
    Multiplicative.ofAdd (((gamEquiv hb hzz hH h : ↥(gam hb hzz hH)) : GL (Fin 3) FieldFour) *ᵥ
      Multiplicative.toAdd ((coordEquiv hb).symm s))
  rw [MulEquiv.symm_apply_apply, coe_gamEquiv, glOf_mulVec, symm_apply_eq_linOf hb hzz]

theorem pow_smul_one {K : Type*} [Field K] (c : K) (n : ℕ) :
    (c • (1 : Matrix (Fin 3) (Fin 3) K)) ^ n = c ^ n • 1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, smul_mul_smul_comm, one_mul, pow_succ]

theorem gam_props [Finite V] (hperf : Group.IsPerfect ↥H) (hZ : Nat.card (Subgroup.center ↥H) = 3)
    (e : ↥H ⧸ Subgroup.center ↥H ≃* alternatingGroup (Fin 6)) {zH : ↥H}
    (hzH : (zH : MulAut V) = z) (hcen : Subgroup.center ↥H = Subgroup.zpowers zH) :
    (∀ g ∈ gam hb hzz hH,
      ((g : GL (Fin 3) FieldFour) : Matrix (Fin 3) (Fin 3) FieldFour).det = 1) ∧
    IsHat ↥(gam hb hzz hH) ↥(alternatingGroup (Fin 6)) ∧
    (∀ g ∈ Subgroup.center ↥(gam hb hzz hH), ∃ c : FieldFour,
      (((g : ↥(gam hb hzz hH)) : GL (Fin 3) FieldFour) : Matrix (Fin 3) (Fin 3) FieldFour) =
        c • 1) := by
  obtain ⟨hq, -⟩ := quasisimple_card hperf hZ e
  set E := gamEquiv hb hzz hH with hE
  have hc : (Subgroup.center ↥H).map (E : ↥H →* ↥(gam hb hzz hH)) =
      Subgroup.center ↥(gam hb hzz hH) := Subgroup.map_center_eq E
  refine ⟨?_, ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv E hq, ?_, ?_⟩, ?_⟩
  · rintro _ ⟨h, rfl⟩
    have hk : commutator ↥H ≤ (Matrix.GeneralLinearGroup.det.comp (glOf hb hzz H hH)).ker :=
      Abelianization.commutator_subset_ker _
    have htop : commutator ↥H = ⊤ := Group.isPerfect_def.1 hperf
    have h1 := hk (htop ▸ Subgroup.mem_top h)
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at h1
    rw [← Matrix.GeneralLinearGroup.val_det_apply, h1, Units.val_one]
  · rw [← hc, Subgroup.card_map_of_injective (f := (E : ↥H →* ↥(gam hb hzz hH))) E.injective, hZ]
  · exact ⟨(QuotientGroup.congr _ _ E hc).symm.trans e⟩
  · intro g hg
    have hg' : E.symm g ∈ Subgroup.center ↥H := by
      rw [← hc] at hg
      obtain ⟨h, hh, rfl⟩ := hg
      change E.symm (E h) ∈ _
      rw [MulEquiv.symm_apply_apply]
      exact hh
    rw [hcen] at hg'
    obtain ⟨n, hn⟩ := (mem_powers_iff_mem_zpowers).2 hg'
    refine ⟨FieldFour.ω ^ n, ?_⟩
    have hn' : zH ^ n = E.symm g := hn
    have hgE : g = E (zH ^ n) := by rw [hn', MulEquiv.apply_symm_apply]
    rw [hgE, map_pow, Subgroup.coe_pow, Units.val_pow_eq_pow_val, coe_gamEquiv,
      glOf_eq_smul hb hzz hH zH hzH, pow_smul_one]

end Model

theorem hatA6SixModel : H13.HatA6SixModel := by
  intro V _ _ hsq2 hV H hperf hZ ⟨e⟩
  obtain ⟨zH, hcen, h3, hfp⟩ := exists_center_fpf hsq2 hV hperf hZ e
  have hsq : ∀ v : V, v * v = 1 := fun v => by rw [← pow_two]; exact hsq2 v
  have hzz : ∀ w, (zH : MulAut V) ((zH : MulAut V) w) = w * (zH : MulAut V) w := fun w =>
    H13.zz_eq_of_fpf hsq2 h3 (W := ⊤) (fun _ _ => trivial) (fun w _ hw => hfp w hw) trivial
  obtain ⟨u, hb⟩ := exists_coord hsq hV h3 hfp
  have hH : ∀ x ∈ H, ∀ w, x ((zH : MulAut V) w) = (zH : MulAut V) (x w) := by
    intro x hx w
    have h1 := Subgroup.mem_center_iff.1 (hcen ▸ Subgroup.mem_zpowers zH) ⟨x, hx⟩
    have h2 := congrArg (fun y : ↥H => (y : MulAut V) w) h1
    exact h2
  obtain ⟨hdet, hhat, hcen'⟩ := gam_props hb hzz hH hperf hZ e rfl hcen
  exact ⟨FieldFour, inferInstance, inferInstance, gam hb hzz hH, FieldFour.natCard_eq, hdet,
    hhat, hcen', _, realizesVia_gam hb hzz hH⟩

end CFSG.Quasithin.HatA6
