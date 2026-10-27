module

public import CFSG.Quasithin.Background.HMathieuStd

public section

namespace CFSG.Quasithin.H.Mathieu

open CFSG.Monster.Code

section Generic

variable {numer denom : Subgroup (G6.PermMod 24)} {W : Type*} [CommGroup W]
  {V : Type*} [CommGroup V]

theorem SecCoords.exists_equiv_compat (c : SecCoords numer denom W)
    {Γ : Subgroup (Equiv.Perm (Fin 24))} (hΓ : ∀ σ ∈ Γ, Preserves numer denom σ)
    (π : ↥Γ → MulAut V) (β : ↥(⊤ : Subgroup V) →* ↥numer ⧸ denom.subgroupOf numer)
    (hβs : ∀ q, ∃ u, β u = q) (hβ1 : ∀ v : V, β ⟨v, Subgroup.mem_top v⟩ = 1 → v = 1)
    (hβa : ∀ (γ : ↥Γ) (v : V) (m : ↥numer), β ⟨v, Subgroup.mem_top v⟩ = QuotientGroup.mk m →
      β ⟨π γ v, Subgroup.mem_top _⟩ =
        QuotientGroup.mk ⟨G6.permAct 24 γ m, (hΓ γ γ.2).1 m m.2⟩) :
    ∃ e : V ≃* W, (∀ (γ : ↥Γ) (v : V), e (π γ v) = c.rho Γ hΓ γ (e v)) ∧
      ∀ (v : V) (m : ↥numer), β ⟨v, Subgroup.mem_top v⟩ = QuotientGroup.mk m ↔
        e v = c.κ m := by
  let κs : ↥numer →* W := c.κ.comp numer.subtype
  have hle : denom.subgroupOf numer ≤ κs.ker := by
    intro m hm
    rw [MonoidHom.mem_ker]
    exact (c.ker_iff m m.2).2 (Subgroup.mem_subgroupOf.1 hm)
  let κb : ↥numer ⧸ denom.subgroupOf numer →* W := QuotientGroup.lift _ κs hle
  have hκb : ∀ m : ↥numer, κb (QuotientGroup.mk m) = c.κ m := fun _ => rfl
  let e₀ : V →* W := κb.comp (β.comp (Subgroup.topEquiv (G := V)).symm.toMonoidHom)
  have he₀ : ∀ v, e₀ v = κb (β ⟨v, Subgroup.mem_top v⟩) := fun _ => rfl
  have hinj : Function.Injective e₀ := by
    rw [injective_iff_map_eq_one]
    intro v hv
    rw [he₀] at hv
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β ⟨v, Subgroup.mem_top v⟩)
    rw [← hm, hκb] at hv
    have hmd : (m : G6.PermMod 24) ∈ denom := (c.ker_iff m m.2).1 hv
    have hm1 : (QuotientGroup.mk m : ↥numer ⧸ denom.subgroupOf numer) = 1 :=
      (QuotientGroup.eq_one_iff m).2 (Subgroup.mem_subgroupOf.2 hmd)
    exact hβ1 v (hm.symm.trans hm1)
  have hsurj : Function.Surjective e₀ := by
    intro w
    obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk ⟨c.lift w, c.lift_mem w⟩)
    refine ⟨(u : V), ?_⟩
    rw [he₀]
    have : (⟨(u : V), Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup V)) = u := rfl
    rw [this, hu, hκb]
    exact c.κ_lift w
  have hbij : Function.Bijective e₀ := ⟨hinj, hsurj⟩
  refine ⟨MulEquiv.ofBijective e₀ hbij, fun γ v => ?_, fun v m => ?_⟩
  · rw [MulEquiv.ofBijective_apply, MulEquiv.ofBijective_apply]
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β ⟨v, Subgroup.mem_top v⟩)
    rw [he₀, he₀, hβa γ v m hm.symm, hκb, ← hm, hκb]
    exact c.κ_permAct_rho Γ hΓ γ m.2
  · rw [MulEquiv.ofBijective_apply, he₀]
    constructor
    · intro h
      rw [h, hκb]
    · intro h
      obtain ⟨m', hm'⟩ := QuotientGroup.mk_surjective (β ⟨v, Subgroup.mem_top v⟩)
      rw [← hm', hκb] at h
      rw [← hm']
      refine QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 ?_)
      refine (c.ker_iff _ (numer.mul_mem (numer.inv_mem m'.2) m.2)).1 ?_
      rw [map_mul, map_inv, h, inv_mul_cancel]

theorem SecCoords.exists_map_eq_compat (c : SecCoords numer denom W)
    {Γ : Subgroup (Equiv.Perm (Fin 24))} (hΓ : ∀ σ ∈ Γ, Preserves numer denom σ)
    {H : Subgroup (MulAut V)} (h : (FFModel.golaySec Γ numer denom).Realizes H ⊤ ⊥) :
    ∃ (π : (FFModel.golaySec Γ numer denom).Gam →* ↥H)
      (β : ↥(⊤ : Subgroup V) →* ↥numer ⧸ denom.subgroupOf numer),
      RealizesBy (FFModel.golaySec Γ numer denom) H ⊤ ⊥ π β ∧
      ∃ e : V ≃* W, H.map (congrHom e) = (c.rho Γ hΓ).range ∧
        ∀ (v : V) (m : ↥numer), β ⟨v, Subgroup.mem_top v⟩ = QuotientGroup.mk m ↔
          e v = c.κ m := by
  obtain ⟨π, β, hb⟩ := (realizes_iff _ _ _ _).1 h
  have hb' := hb
  obtain ⟨-, -, -, -, -, -, -, hβs, hβ1, hβa⟩ := hb'
  obtain ⟨e, he, hcompat⟩ := c.exists_equiv_compat hΓ (fun γ => ((π γ : ↥H) : MulAut V)) β hβs
    (fun v hv => Subgroup.mem_bot.1 ((hβ1 _).1 hv))
    (fun γ v m hm => hβa γ ⟨v, Subgroup.mem_top v⟩ m (Subgroup.mem_top _) _ hm)
  refine ⟨π, β, hb, e, ?_, hcompat⟩
  have hπ : ∀ γ : ↥Γ, congrHom e ((π γ : ↥H) : MulAut V) = c.rho Γ hΓ γ := by
    intro γ
    ext w
    rw [congrHom_apply, he, MulEquiv.apply_symm_apply]
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨γ, hγ⟩ := hb.1 ⟨x, hx⟩
    refine ⟨γ, ?_⟩
    have h1 := hπ γ
    rw [hγ] at h1
    exact h1.symm
  · rintro _ ⟨γ, rfl⟩
    exact ⟨_, (π γ).2, hπ γ⟩

end Generic

variable {V : Type*} [CommGroup V] {L : Subgroup (MulAut V)}

theorem cocode22_stdO (h : MathieuCocode22 L ⊤ ⊥) :
    ∃ e : V ≃* W10, L.map (congrHom e) = (rho10 mog22 mog22_le_mog22plus).range ∧
      ∀ (v : V) (j : Fin 24), j ≠ 0 → j ≠ 1 → e v = cocode22Coords.κ (pairVec 0 j) →
        IsCocodeO2 L v := by
  obtain ⟨x, y, hxy, hr⟩ := h
  obtain ⟨τ, hτ, hτ0, hτ1⟩ := CFSG.Monster.B.TwoA.autPerm_maps_two x y hxy
  obtain ⟨hn, hC⟩ := preserves_iff_of_mem hτ
  have hτ0' : τ⁻¹ x = 0 := by rw [← hτ0]; simp
  have hτ1' : τ⁻¹ y = 1 := by rw [← hτ1]; simp
  have hd : ∀ m, m ∈ golayC ⊔ Subgroup.zpowers (pairVec x y) ↔
      G6.permAct 24 τ⁻¹ m ∈ golayC ⊔ Subgroup.zpowers (pairVec 0 1) := by
    intro m
    refine (mem_sup_zpowers_iff' (pairVec_sq x y) m).trans
      (Iff.trans ?_ (mem_sup_zpowers_iff' (pairVec_sq 0 1) _).symm)
    rw [hC m, hC (m * pairVec x y), map_mul, permAct_pairVec, hτ0', hτ1']
  have hΓxy : ∀ σ ∈ AutPerm ⊓ stab x ⊓ stab y,
      Preserves (G6.coreMod 24) (golayC ⊔ Subgroup.zpowers (pairVec x y)) σ := by
    intro σ hσ
    obtain ⟨h1, h2⟩ := preserves_cocode hσ.1.1
    have hσx : σ x = x := (mem_stab_iff x σ).1 hσ.1.2
    have hσy : σ y = y := (mem_stab_iff y σ).1 hσ.2
    refine ⟨h1, fun m hm => ?_⟩
    refine (mem_sup_zpowers_iff' (pairVec_sq x y) _).2 ?_
    rcases (mem_sup_zpowers_iff' (pairVec_sq x y) m).1 hm with hm | hm
    · exact Or.inl (h2 _ hm)
    · right
      have := h2 _ hm
      rwa [map_mul, permAct_pairVec, hσx, hσy] at this
  obtain ⟨π, β, hRB, e, he, hcompat⟩ :=
    (cocode22Coords.conj τ hn hd).exists_map_eq_compat hΓxy hr
  refine ⟨e, he.trans ?_, fun v j hj0 hj1 hev => ?_⟩
  · refine cocode22Coords.range_rho_conj τ hn hd _ hΓxy fun σ => ?_
    simp only [Subgroup.mem_inf, mem_stab_iff, Equiv.Perm.mul_apply, hτ0, hτ1]
    constructor
    · rintro ⟨⟨hσ, hσx⟩, hσy⟩
      refine ⟨⟨AutPerm.mul_mem (AutPerm.mul_mem (AutPerm.inv_mem hτ) hσ) hτ, ?_⟩, ?_⟩
      · rw [hσx, hτ0']
      · rw [hσy, hτ1']
    · rintro ⟨⟨hσ, hσx⟩, hσy⟩
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · have := AutPerm.mul_mem (AutPerm.mul_mem hτ hσ) (AutPerm.inv_mem hτ)
        simpa [mul_assoc] using this
      · have := congrArg τ hσx
        simpa [hτ0] using this
      · have := congrArg τ hσy
        simpa [hτ1] using this
  ·
    have hκ : (cocode22Coords.conj τ hn hd).κ (pairVec x (τ j)) =
        cocode22Coords.κ (pairVec 0 j) := by
      change cocode22Coords.κ (G6.permAct 24 τ⁻¹ (pairVec x (τ j))) = _
      rw [permAct_pairVec, hτ0']
      simp
    have hβv := (hcompat v ⟨pairVec x (τ j), pairVec_mem_coreMod _ _⟩).2 (hev.trans hκ.symm)
    refine Or.inr (Or.inr ⟨x, y, hxy, π, β, hRB, τ j, ?_, ?_, hβv⟩)
    · rw [← hτ0]
      exact fun h => hj0 (τ.injective h).symm
    · rw [← hτ1]
      exact fun h => hj1 (τ.injective h).symm

theorem cocode23_stdO (h : MathieuCocode23 L ⊤ ⊥) :
    ∃ e : V ≃* W11, L.map (congrHom e) = (rho11 mog23 inf_le_left).range ∧
      ∀ (v : V) (j : Fin 24), j ≠ 0 → e v = cocodeCoords.κ (pairVec 0 j) →
        IsCocodeO2 L v := by
  obtain ⟨x, hx⟩ := h
  obtain ⟨τ, hτ, hτ0, -⟩ := CFSG.Monster.B.TwoA.autPerm_maps_two x (x + 1) (by
    intro h
    have := congrArg Fin.val h
    simp [Fin.val_add] at this
    omega)
  obtain ⟨hn, hd⟩ := preserves_iff_of_mem hτ
  have hΓx : ∀ σ ∈ AutPerm ⊓ stab x, Preserves (G6.coreMod 24) golayC σ :=
    fun _ hσ => preserves_cocode hσ.1
  have hτ0' : τ⁻¹ x = 0 := by rw [← hτ0, ← Equiv.Perm.mul_apply, inv_mul_cancel]; rfl
  obtain ⟨π, β, hRB, e, he, hcompat⟩ := (cocodeCoords.conj τ hn hd).exists_map_eq_compat hΓx hx
  refine ⟨e, he.trans ?_, fun v j hj0 hev => ?_⟩
  · refine cocodeCoords.range_rho_conj τ hn hd _ hΓx fun σ => ?_
    simp only [Subgroup.mem_inf, mem_stab_iff, Equiv.Perm.mul_apply, hτ0]
    constructor
    · rintro ⟨hσ, hσx⟩
      refine ⟨AutPerm.mul_mem (AutPerm.mul_mem (AutPerm.inv_mem hτ) hσ) hτ, ?_⟩
      rw [hσx, hτ0']
    · rintro ⟨hσ, hσx⟩
      refine ⟨?_, ?_⟩
      · have := AutPerm.mul_mem (AutPerm.mul_mem hτ hσ) (AutPerm.inv_mem hτ)
        simpa [mul_assoc] using this
      · have := congrArg τ hσx
        simpa [hτ0] using this
  · have hκ : (cocodeCoords.conj τ hn hd).κ (pairVec x (τ j)) = cocodeCoords.κ (pairVec 0 j) := by
      change cocodeCoords.κ (G6.permAct 24 τ⁻¹ (pairVec x (τ j))) = _
      rw [permAct_pairVec, hτ0']
      simp
    have hβv := (hcompat v ⟨pairVec x (τ j), pairVec_mem_coreMod _ _⟩).2 (hev.trans hκ.symm)
    refine Or.inr (Or.inl ⟨x, π, β, hRB, τ j, ?_, hβv⟩)
    rw [← hτ0]
    exact fun h => hj0 (τ.injective h).symm

theorem cocode24_stdO (h : MathieuCocode24 L ⊤ ⊥) :
    ∃ e : V ≃* W11, L.map (congrHom e) = (rho11 AutPerm le_rfl).range ∧
      ∀ (v : V) (i j : Fin 24), i ≠ j → e v = cocodeCoords.κ (pairVec i j) →
        IsCocodeO2 L v := by
  obtain ⟨π, β, hRB, e, he, hcompat⟩ :=
    cocodeCoords.exists_map_eq_compat (fun _ hσ => preserves_cocode hσ) h
  refine ⟨e, he, fun v i j hij hev => ?_⟩
  exact Or.inl ⟨π, β, hRB, i, j, hij,
    (hcompat v ⟨pairVec i j, pairVec_mem_coreMod _ _⟩).2 hev⟩

end CFSG.Quasithin.H.Mathieu
