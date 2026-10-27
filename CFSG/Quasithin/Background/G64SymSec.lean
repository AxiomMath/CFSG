module

public import CFSG.Quasithin.Background.G64RealizeSec
public import CFSG.Quasithin.Background.G64C512Ext
public import CFSG.Quasithin.Background.B4ModelsAction

public section

namespace CFSG.Quasithin.G64

open CFSG.Quasithin CFSG.Assembly.LowTwoRank Equiv Equiv.Perm

variable {V : Type*} [CommGroup V]

theorem permModel_faithful {n : ℕ} (hn : 5 ≤ n) {Z' : Subgroup (G6.PermMod n)}
    (hZ' : Z' ≤ Subgroup.zpowers (G6.allOnes n) ⊓ G6.coreMod n) : (permModel n Z').Faithful := by
  intro (σ : Perm (Fin n)) hσ
  exact symDn_faithful hn σ fun m hm => hZ' (hσ m hm)

theorem altDn_faithful {n : ℕ} (hn : 5 ≤ n) : (FFModel.altDn n).Faithful := by
  intro (σ : ↥(alternatingGroup (Fin n))) hσ
  have := symDn_faithful hn (σ : Perm (Fin n)) fun m hm => hσ m hm
  exact Subtype.ext this

theorem a7Four_faithful
    (α : ↥(alternatingGroup (Fin 8)) ≃* Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)) :
    (FFModel.a7Four α).Faithful := by
  intro (σ : ↥(alternatingGroup (Fin 7))) hσ
  have hmat : α (altLift7 σ) = 1 := by
    apply Units.ext
    refine Matrix.ext_of_mulVec_single fun j => ?_
    have h3 := Subgroup.mem_bot.mp (hσ (Multiplicative.ofAdd (Pi.single j 1)) trivial)
    have h3' : a7Act α σ (Multiplicative.ofAdd (Pi.single j 1)) =
        Multiplicative.ofAdd (Pi.single j 1) := mul_inv_eq_one.1 h3
    rw [Units.val_one, Matrix.one_mulVec]
    exact congrArg Multiplicative.toAdd h3'
  have h1 : altLift7 σ = 1 := α.injective (by rw [hmat, map_one])
  have h2 : (Perm.viaEmbeddingHom (Fin.castSuccEmb : Fin 7 ↪ Fin 8)) (σ : Perm (Fin 7)) = 1 := by
    have := congrArg Subtype.val h1
    exact this
  exact Subtype.ext (Perm.viaEmbeddingHom_injective _ (h2.trans (map_one _).symm))

theorem permModel_isActionModel {n : ℕ} {Z' : Subgroup (G6.PermMod n)}
    (hZ'c : Z' ≤ G6.coreMod n) (hZ'i : ∀ σ : Perm (Fin n), ∀ m ∈ Z', G6.permAct n σ m ∈ Z') :
    (permModel n Z').IsActionModel where
  act_mul σ x y := map_mul (G6.permAct n σ) x y
  act_one x := permAct_one_act n x
  act_mul_act σ τ x := permAct_mul_act n σ τ x
  sec_inv σ _ hm := G6.permAct_mem_coreMod σ hm
  ker_inv σ m hm := hZ'i σ m hm
  ker_le := hZ'c

theorem realizesVia_modAct {D : FFModel} (hD : D.IsActionModel) :
    D.RealizesVia hD.modAct.range ⊤ ⊥ hD.modAct.rangeRestrict := by
  refine ⟨MonoidHom.rangeRestrict_surjective _, le_top, hD.ker_le,
    fun _ u _ => trivial, fun _ z hz => by simpa using hz, hD.sec_inv, hD.ker_inv, ?_⟩
  refine ⟨Subgroup.topEquiv.toMonoidHom, fun q => ⟨⟨q, trivial⟩, rfl⟩, fun u => ?_, ?_⟩
  · simp only [Subgroup.mem_bot]
    rfl
  · intro γ u m hu hm hum
    have hu' : (u : D.Mod) = QuotientGroup.mk m := hum
    show hD.modAct γ (u : D.Mod) = QuotientGroup.mk ⟨D.act γ (m : D.Amb), hm⟩
    rw [hu', FFModel.IsActionModel.modAct_apply, FFModel.IsActionModel.modEnd_mk]
    rfl

theorem modAct_injective {D : FFModel} (hD : D.IsActionModel) (hf : D.Faithful) :
    Function.Injective hD.modAct := by
  rw [injective_iff_map_eq_one]
  intro γ hγ
  apply hf
  intro m hm
  have h1 := congrArg (fun f : MulAut D.Mod => f (QuotientGroup.mk ⟨m, hm⟩)) hγ
  simp only [MulAut.one_apply] at h1
  rw [FFModel.IsActionModel.modAct_apply, FFModel.IsActionModel.modEnd_mk] at h1
  have h2 := QuotientGroup.eq.mp h1
  have h3 : (⟨D.act γ m, hD.sec_inv γ m hm⟩ : ↥D.sec)⁻¹ * ⟨m, hm⟩ ∈
      D.ker.subgroupOf D.sec := h2
  rw [Subgroup.mem_subgroupOf] at h3
  have h4 := D.ker.inv_mem h3
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv] at h4
  rw [mul_comm]
  exact h4

theorem isSwap_of_section (hV2 : ∀ v : V, v ^ 2 = 1) {n : ℕ} (hn : 5 ≤ n)
    {Z' : Subgroup (G6.PermMod n)} (hZ' : Z' ≤ Subgroup.zpowers (G6.allOnes n) ⊓ G6.coreMod n)
    {H : Subgroup (MulAut V)} {U Z : Subgroup V} {π : Perm (Fin n) →* ↥H}
    (h : (permModel n Z').RealizesVia H U Z π) {σ : Perm (Fin n)} (hσ2 : σ ^ 2 = 1)
    (hmove : ∃ u ∈ U, ((π σ : ↥H) : MulAut V) u * u⁻¹ ∉ Z)
    (hrank : ∃ w : V, ∀ u ∈ U, ((π σ : ↥H) : MulAut V) u * u⁻¹ ∈ Z ⊔ Subgroup.zpowers w) :
    σ.IsSwap := by
  classical
  set D := permModel n Z' with hD
  have hAM : D.IsActionModel := permModel_isActionModel (fun m hm => (hZ' hm).2)
    (fun τ m hm => h.2.2.2.2.2.2.1 τ m hm)
  have hf : D.Faithful := permModel_faithful hn hZ'
  set ρ : Perm (Fin n) →* MulAut D.Mod := hAM.modAct with hρ
  have hreal := realizesVia_modAct hAM
  have hinj : Function.Injective ρ.rangeRestrict := by
    intro x y hxy
    exact modAct_injective hAM hf (congrArg Subtype.val hxy)
  have hσmem : ρ σ ∈ ρ.range := ⟨σ, rfl⟩
  obtain ⟨_, _, _, hHU, _, hsec, _, β, hβs, hβk, hβe⟩ := h
  obtain ⟨w, hw⟩ := hrank
  obtain ⟨u₁, hu₁, hmv⟩ := hmove
  have hHU' : ∀ u ∈ U, ((π σ : ↥H) : MulAut V) u ∈ U := fun u hu => hHU (π σ) u hu
  have hβe' : ∀ (u : ↥U) (m : ↥D.sec) (hu : ((π σ : ↥H) : MulAut V) u ∈ U)
      (hm : G6.permAct n σ ((m : D.Amb) : G6.PermMod n) ∈ G6.coreMod n),
      β u = QuotientGroup.mk m →
        β ⟨_, hu⟩ = QuotientGroup.mk (⟨G6.permAct n σ ((m : D.Amb) : G6.PermMod n), hm⟩ : ↥D.sec) :=
    fun u m hu hm hum => hβe σ u m hu hm hum
  have hβc : ∀ u : ↥U, β ⟨_, U.mul_mem (hHU' u u.2) (U.inv_mem u.2)⟩ =
      ρ σ (β u) * (β u)⁻¹ := by
    intro u
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β u)
    have hact : G6.permAct n σ ((m : D.Amb) : G6.PermMod n) ∈ G6.coreMod n :=
      G6.permAct_mem_coreMod σ m.2
    have h1 := hβe' u m (hHU' u u.2) hact hm.symm
    have h2 : ρ σ (β u) =
        QuotientGroup.mk (⟨G6.permAct n σ ((m : D.Amb) : G6.PermMod n), hact⟩ : ↥D.sec) := by
      rw [← hm]
      rfl
    calc β ⟨_, U.mul_mem (hHU' u u.2) (U.inv_mem u.2)⟩ = β (⟨_, hHU' u u.2⟩ * u⁻¹) := rfl
      _ = β ⟨_, hHU' u u.2⟩ * (β u)⁻¹ := by rw [map_mul, map_inv]
      _ = ρ σ (β u) * (β u)⁻¹ := by rw [h1, h2]
  set y₀ := β ⟨_, U.mul_mem (hHU' u₁ hu₁) (U.inv_mem hu₁)⟩ with hy₀
  have hy₀1 : y₀ ≠ 1 := fun h1 => hmv ((hβk _).1 h1)
  have hy₀2 : y₀ ^ 2 = 1 := by
    rw [hy₀, ← map_pow]
    have : (⟨_, U.mul_mem (hHU' u₁ hu₁) (U.inv_mem hu₁)⟩ : ↥U) ^ 2 = 1 :=
      Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hV2 _)
    rw [this, map_one]
  have hval : ∀ u : ↥U, ρ σ (β u) * (β u)⁻¹ = 1 ∨ ρ σ (β u) * (β u)⁻¹ = y₀ := by
    intro u
    rw [← hβc u]
    obtain ⟨z, hz, x, hx, hzx⟩ := Subgroup.mem_sup.1 (hw u u.2)
    obtain ⟨z₁, hz₁, x₁, hx₁, hzx₁⟩ := Subgroup.mem_sup.1 (hw u₁ hu₁)
    rcases eq_one_or_eq_of_mem_zpowers' (hV2 w) hx with hx' | hx'
    · left
      rw [hβk]
      show ((π σ : ↥H) : MulAut V) u * (u : V)⁻¹ ∈ Z
      rw [← hzx, hx', mul_one]
      exact hz
    · right
      rcases eq_one_or_eq_of_mem_zpowers' (hV2 w) hx₁ with hx₁' | hx₁'
      · exfalso
        apply hmv
        rw [← hzx₁, hx₁', mul_one]
        exact hz₁
      · rw [hy₀]
        have hdiff : (((⟨_, U.mul_mem (hHU' u u.2) (U.inv_mem u.2)⟩ : ↥U) *
            (⟨_, U.mul_mem (hHU' u₁ hu₁) (U.inv_mem hu₁)⟩ : ↥U)⁻¹ : ↥U) : V) ∈ Z := by
          show (((π σ : ↥H) : MulAut V) u * (u : V)⁻¹) *
            (((π σ : ↥H) : MulAut V) u₁ * u₁⁻¹)⁻¹ ∈ Z
          rw [← hzx, ← hzx₁, hx', hx₁']
          have : z * w * (z₁ * w)⁻¹ = z * z₁⁻¹ := by group
          rw [this]
          exact Z.mul_mem hz (Z.inv_mem hz₁)
        have h0 := (hβk _).2 hdiff
        rw [map_mul, map_inv, mul_inv_eq_one] at h0
        exact h0
  have hσρ : ∀ k : ℤ, ρ σ ^ k = 1 ∨ ρ σ ^ k = ρ σ := by
    intro k
    have h2 : ρ σ ^ 2 = 1 := by rw [← map_pow, hσ2, map_one]
    exact eq_one_or_eq_of_mem_zpowers' h2 (Subgroup.zpow_mem_zpowers _ k)
  have hle : commV (Subgroup.zpowers (ρ σ)) ≤ Subgroup.zpowers y₀ := by
    rw [G6.commV_le_iff]
    intro x hx q
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨u, rfl⟩ := hβs q
    rcases hσρ k with h1 | h1 <;> rw [h1]
    · simp
    · rcases hval u with h2 | h2 <;> rw [h2]
      · exact Subgroup.one_mem _
      · exact Subgroup.mem_zpowers y₀
  have hge : Subgroup.zpowers y₀ ≤ commV (Subgroup.zpowers (ρ σ)) := by
    rw [Subgroup.zpowers_le]
    have h1 : y₀ = ρ σ (β ⟨u₁, hu₁⟩) * (β ⟨u₁, hu₁⟩)⁻¹ := hβc ⟨u₁, hu₁⟩
    rw [h1]
    exact G6.mem_commV_of_mem (Subgroup.mem_zpowers _) _
  have hcard : Nat.card (commV (Subgroup.zpowers (ρ σ))) = 2 := by
    rw [le_antisymm hle hge, Nat.card_zpowers]
    exact orderOf_eq_prime hy₀2 hy₀1
  have hswap := isSwap_of_realization hn hZ' hreal hinj hσmem hcard
  convert hswap using 1
  exact ((MulEquiv.symm_apply_eq _).2 rfl).symm

theorem card_biSup_le {M : Type*} [CommGroup M] [Finite M] {ι : Type*} [DecidableEq ι]
    (A : ι → Subgroup M) (s : Finset ι) :
    Nat.card ↥(⨆ i ∈ s, A i) ≤ ∏ i ∈ s, Nat.card (A i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.iSup_insert, Finset.prod_insert hj]
    exact (card_sup_le _ _).trans (Nat.mul_le_mul_left _ ih)

theorem card_commV_le_of_swap [Finite V] {n : ℕ} {H : Subgroup (MulAut V)}
    (θ : ↥H ≃* Perm (Fin (n + 1))) {a : MulAut V} (ha : a ∈ H) (hsw : (θ ⟨a, ha⟩).IsSwap)
    (htr : Nat.card (commV (Subgroup.zpowers a)) = 2) :
    Nat.card (commV H) ≤ 2 ^ n := by
  classical
  set f : Perm (Fin (n + 1)) →* MulAut V := H.subtype.comp θ.symm.toMonoidHom with hf
  set g : Fin n → MulAut V := fun i => f (swap i.castSucc i.succ) with hg
  have hgt : ∀ i, Nat.card (commV (Subgroup.zpowers (g i))) = 2 := by
    intro i
    obtain ⟨x, y, hxy, hxy'⟩ := hsw
    obtain ⟨c, hc⟩ := isConj_iff.1 (isConj_swap hxy (Fin.castSucc_lt_succ (i := i)).ne)
    have : g i = ((θ.symm c : ↥H) : MulAut V) * a * ((θ.symm c : ↥H) : MulAut V)⁻¹ := by
      rw [hg]
      simp only [hf, MonoidHom.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom]
      rw [← hc, ← hxy', map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
      rfl
    rw [this, G6.card_commV_zpowers_conj, htr]
  have hH : H ≤ Subgroup.closure (Set.range g) := by
    intro x hx
    have hx' : θ ⟨x, hx⟩ ∈
        Submonoid.closure (Set.range fun i : Fin n => swap i.castSucc i.succ) := by
      rw [mclosure_swap_castSucc_succ]
      trivial
    have h1 : f (θ ⟨x, hx⟩) ∈ (Submonoid.closure (Set.range fun i : Fin n =>
        swap i.castSucc i.succ)).map f := Submonoid.mem_map_of_mem f hx'
    rw [MonoidHom.map_mclosure] at h1
    have h2 : f (θ ⟨x, hx⟩) = x := by simp [hf]
    rw [h2] at h1
    have hcl : Submonoid.closure (f '' Set.range fun i : Fin n => swap i.castSucc i.succ) ≤
        (Subgroup.closure (Set.range g)).toSubmonoid := by
      rw [Submonoid.closure_le]
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      exact Subgroup.subset_closure ⟨i, rfl⟩
    exact hcl h1
  have hle : commV H ≤ ⨆ i ∈ (Finset.univ : Finset (Fin n)),
      commV (Subgroup.zpowers (g i)) := by
    refine (G6.commV_mono hH).trans (G6.commV_closure_le ?_)
    rintro _ ⟨i, rfl⟩ v
    exact (le_iSup₂ (f := fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
      commV (Subgroup.zpowers (g i))) i (Finset.mem_univ i))
      (G6.mem_commV_of_mem (Subgroup.mem_zpowers _) v)
  calc Nat.card (commV H)
      ≤ Nat.card ↥(⨆ i ∈ (Finset.univ : Finset (Fin n)), commV (Subgroup.zpowers (g i))) :=
        Subgroup.card_le_of_le hle
    _ ≤ ∏ i ∈ (Finset.univ : Finset (Fin n)), Nat.card (commV (Subgroup.zpowers (g i))) :=
        card_biSup_le _ _
    _ = 2 ^ n := by simp [hgt]

end CFSG.Quasithin.G64
