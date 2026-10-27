module

public import CFSG.Quasithin.Background.HMathieuO2Cert
public import CFSG.Quasithin.Background.HMathieuStdO

public section

namespace CFSG.Quasithin.H.Mathieu

open CFSG.Monster.Code

section Generic

variable {V W : Type*} [CommGroup V] [CommGroup W]

@[expose] def stabV (L : Subgroup (MulAut V)) (v : V) : Subgroup (MulAut V) :=
  L ⊓ MulAction.stabilizer (MulAut V) v

theorem mem_stabV {L : Subgroup (MulAut V)} {v : V} {φ : MulAut V} :
    φ ∈ stabV L v ↔ φ ∈ L ∧ φ v = v :=
  and_congr Iff.rfl (MulAction.mem_stabilizer_iff.trans (by rw [MulAut.smul_def]))

@[expose] def O2Data (L : Subgroup (MulAut V)) (v : V) (N : ℕ) : Prop :=
  IsSimpleGroup ↥(perfectCore (stabV L v)) ∧ Nat.card ↥(perfectCore (stabV L v)) = N ∧
    commV (perfectCore (stabV L v)) = ⊤ ∧
    Subgroup.centralizer (perfectCore (stabV L v) : Set (MulAut V)) = ⊥

theorem stabV_map_congrHom (e : V ≃* W) (L : Subgroup (MulAut V)) (v : V) :
    stabV (L.map (congrHom e)) (e v) = (stabV L v).map (congrHom e) := by
  ext ψ
  constructor
  · intro h
    obtain ⟨⟨φ, hφ, rfl⟩, hψ⟩ := mem_stabV.1 h
    refine ⟨φ, mem_stabV.2 ⟨hφ, ?_⟩, rfl⟩
    rw [congrHom_apply, MulEquiv.symm_apply_apply] at hψ
    exact e.injective hψ
  · rintro ⟨φ, hφ, rfl⟩
    obtain ⟨hφL, hφv⟩ := mem_stabV.1 hφ
    refine mem_stabV.2 ⟨⟨φ, hφL, rfl⟩, ?_⟩
    rw [congrHom_apply, MulEquiv.symm_apply_apply, hφv]

theorem O2Data.of_map [Finite V] [Finite W] (e : V ≃* W) {L : Subgroup (MulAut V)} {v : V}
    {N : ℕ} (h : O2Data (L.map (congrHom e)) (e v) N) : O2Data L v N := by
  have := finite_mulAut V
  have := finite_mulAut W
  set Y := perfectCore (stabV L v) with hYdef
  have hY : perfectCore (stabV (L.map (congrHom e)) (e v)) = Y.map (congrHom e) := by
    rw [stabV_map_congrHom, map_perfectCore]
  rw [O2Data, hY] at h
  obtain ⟨hs, hc, hcomm, hcen⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := hs
    exact (Y.equivMapOfInjective _ (congrHom_injective e)).isSimpleGroup
  · rw [← hc, Subgroup.card_map_of_injective (congrHom_injective e)]
  · rw [eq_top_iff]
    intro u _
    have hle : commV (Y.map (congrHom e)) ≤ (commV Y).map e.toMonoidHom := by
      rw [commV, Subgroup.closure_le]
      rintro _ ⟨ψ, ⟨φ, hφ, rfl⟩, w, rfl⟩
      refine ⟨φ (e.symm w) * (e.symm w)⁻¹, Subgroup.subset_closure ⟨φ, hφ, e.symm w, rfl⟩, ?_⟩
      rw [MulEquiv.coe_toMonoidHom, map_mul, map_inv, MulEquiv.apply_symm_apply,
        congrHom_apply]
    obtain ⟨u', hu', he⟩ := hle (show e u ∈ commV (Y.map (congrHom e)) by
      rw [hcomm]; exact Subgroup.mem_top _)
    rw [show u = u' from e.injective he.symm]
    exact hu'
  · rw [eq_bot_iff]
    intro c hc'
    have hmem : congrHom e c ∈ Subgroup.centralizer (Y.map (congrHom e) : Set (MulAut W)) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨φ, hφ, rfl⟩
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.1 hc' φ hφ]
    rw [hcen, Subgroup.mem_bot] at hmem
    rw [Subgroup.mem_bot]
    exact congrHom_injective e (hmem.trans (map_one _).symm)

theorem O2Data.of_normalizer [Finite V] {L : Subgroup (MulAut V)} {μ : MulAut V}
    (hμ : μ ∈ Subgroup.normalizer (L : Set (MulAut V))) {v : V} {N : ℕ} (h : O2Data L v N) :
    O2Data L (μ v) N := by
  have hμi : μ⁻¹ ∈ Subgroup.normalizer (L : Set (MulAut V)) := inv_mem hμ
  have hconj : ∀ ψ : MulAut V, congrHom (MulEquiv.symm μ) ψ = μ⁻¹ * ψ * μ⁻¹⁻¹ := by
    intro ψ
    ext w
    rw [congrHom_apply, inv_inv, MulAut.mul_apply, MulAut.mul_apply, MulEquiv.symm_symm]
    rfl
  have hL : L.map (congrHom (MulEquiv.symm μ)) = L := by
    ext φ
    constructor
    · rintro ⟨ψ, hψ, rfl⟩
      rw [hconj]
      exact (Subgroup.mem_normalizer_iff.1 hμi ψ).1 hψ
    · intro hφ
      refine ⟨μ * φ * μ⁻¹, (Subgroup.mem_normalizer_iff.1 hμ φ).1 hφ, ?_⟩
      rw [hconj]
      group
  refine O2Data.of_map (MulEquiv.symm μ) ?_
  rw [hL, MulEquiv.symm_apply_apply]
  exact h

theorem O2Data.of_eq {L Y : Subgroup (MulAut V)} {v : V} {N : ℕ}
    (hY : perfectCore (stabV L v) = Y) (hs : IsSimpleGroup ↥Y) (hc : Nat.card ↥Y = N)
    (hcomm : commV Y = ⊤) (hcen : Subgroup.centralizer (Y : Set (MulAut V)) = ⊥) :
    O2Data L v N := by
  subst hY
  exact ⟨hs, hc, hcomm, hcen⟩

theorem O2Data.of_map' [Finite V] [Finite W] (e : V ≃* W) {L : Subgroup (MulAut V)}
    {L' : Subgroup (MulAut W)} {v : V} {v' : W} {N : ℕ} (he : L.map (congrHom e) = L')
    (hev : e v = v') (h : O2Data L' v' N) : O2Data L v N := by
  subst he hev
  exact O2Data.of_map e h

end Generic

theorem perfectCore_map_subgroupOf {G X : Type*} [Group G] [Group X] [Finite G] [Finite X]
    {P Γ : Subgroup G} (hΓP : Γ ≤ P) (f : ↥P →* X) :
    perfectCore ((Γ.subgroupOf P).map f) = ((perfectCore Γ).subgroupOf P).map f := by
  rw [← map_perfectCore]
  congr 1
  apply Subgroup.map_injective P.subtype_injective
  rw [map_perfectCore, Subgroup.map_subgroupOf_eq_of_le hΓP,
    Subgroup.map_subgroupOf_eq_of_le ((perfectCore_le Γ).trans hΓP)]

theorem natCard_Wn (n : ℕ) : Nat.card (Wn n) = 2 ^ n := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_fin]

theorem natCard_W10 : Nat.card W10 = 2 ^ 10 := natCard_Wn 10

theorem natCard_W11 : Nat.card W11 = 2 ^ 11 := natCard_Wn 11

theorem stabV_img10_mog22
    : stabV (img10 mog22) (toW 10 48) = img10 mog21 := by
  ext φ
  refine Iff.trans mem_stabV ?_
  constructor
  · rintro ⟨⟨σ, hσ, rfl⟩, hfix⟩
    have hσ' := Subgroup.mem_subgroupOf.1 hσ
    have h0 : (σ : Equiv.Perm (Fin 24)) 0 = 0 := (mem_stab_iff 0 _).1 hσ'.1.2
    have h1 : (σ : Equiv.Perm (Fin 24)) 1 = 1 := (mem_stab_iff 1 _).1 hσ'.2
    have hfix' : rho10 mog22plus le_rfl σ (cocode22Coords.κ (pairVec 0 2)) =
        cocode22Coords.κ (pairVec 0 2) := by
      rw [kappa22_pairVec_zero_two]
      exact hfix
    rw [rho10_pairVec] at hfix'
    clear hfix
    have hne0 : (σ : Equiv.Perm (Fin 24)) 2 ≠ 0 := fun h =>
      absurd ((σ : Equiv.Perm (Fin 24)).injective (h.trans h0.symm)) (by decide)
    have hne1 : (σ : Equiv.Perm (Fin 24)) 2 ≠ 1 := fun h =>
      absurd ((σ : Equiv.Perm (Fin 24)).injective (h.trans h1.symm)) (by decide)
    have h2 := kappa22_pairVec_inj hne0 hne1 (by decide) (by decide) hfix'
    exact ⟨σ, Subgroup.mem_subgroupOf.2 ⟨hσ', (mem_stab_iff 2 _).2 h2⟩, rfl⟩
  · rintro ⟨σ, hσ, rfl⟩
    have hσ' := Subgroup.mem_subgroupOf.1 hσ
    exact ⟨⟨σ, Subgroup.mem_subgroupOf.2 hσ'.1, rfl⟩, img10_mog21_fix _ ⟨σ, hσ, rfl⟩⟩

theorem stabV_img11_mog23
    : stabV (img11 mog23) (toW 11 95) = img11 mog22 := by
  ext φ
  refine Iff.trans mem_stabV ?_
  constructor
  · rintro ⟨⟨σ, hσ, rfl⟩, hfix⟩
    have hσ' := Subgroup.mem_subgroupOf.1 hσ
    have h0 : (σ : Equiv.Perm (Fin 24)) 0 = 0 := (mem_stab_iff 0 _).1 hσ'.2
    have hfix' : rho11 AutPerm le_rfl σ (cocodeCoords.κ (pairVec 0 1)) =
        cocodeCoords.κ (pairVec 0 1) := by
      rw [kappa11_pairVec_zero_one]
      exact hfix
    rw [rho11_pairVec, h0] at hfix'
    rcases kappa11_pairVec_inj
        (fun h => absurd ((σ : Equiv.Perm (Fin 24)).injective (h.symm.trans h0.symm))
          (by decide)) (by decide) hfix' with ⟨-, h1⟩ | ⟨h, -⟩
    · exact ⟨σ, Subgroup.mem_subgroupOf.2 ⟨hσ', (mem_stab_iff 1 _).2 h1⟩, rfl⟩
    · exact absurd h (by decide)
  · rintro ⟨σ, hσ, rfl⟩
    have hσ' := Subgroup.mem_subgroupOf.1 hσ
    exact ⟨⟨σ, Subgroup.mem_subgroupOf.2 hσ'.1, rfl⟩, img11_mog22_fix _ ⟨σ, hσ, rfl⟩⟩

theorem stabV_img11_autPerm
    : stabV (img11 AutPerm) (toW 11 95) = img11 mog22plus := by
  ext φ
  refine Iff.trans mem_stabV ?_
  constructor
  · rintro ⟨⟨σ, hσ, rfl⟩, hfix⟩
    have hfix' : rho11 AutPerm le_rfl σ (cocodeCoords.κ (pairVec 0 1)) =
        cocodeCoords.κ (pairVec 0 1) := by
      rw [kappa11_pairVec_zero_one]
      exact hfix
    rw [rho11_pairVec] at hfix'
    have hne : (σ : Equiv.Perm (Fin 24)) 0 ≠ (σ : Equiv.Perm (Fin 24)) 1 :=
      (σ : Equiv.Perm (Fin 24)).injective.ne (by decide)
    have hst : (σ : Equiv.Perm (Fin 24)) ∈ stabPair01 := by
      rcases kappa11_pairVec_inj hne (by decide) hfix' with ⟨h0, h1⟩ | ⟨h0, h1⟩
      · exact Or.inl ⟨h0, h1⟩
      · exact Or.inr ⟨h0, h1⟩
    exact ⟨σ, Subgroup.mem_subgroupOf.2 ⟨σ.2, hst⟩, rfl⟩
  · rintro ⟨σ, hσ, rfl⟩
    have hσ' := Subgroup.mem_subgroupOf.1 hσ
    refine ⟨⟨σ, Subgroup.mem_subgroupOf.2 σ.2, rfl⟩, ?_⟩
    have key : rho11 AutPerm le_rfl σ (cocodeCoords.κ (pairVec 0 1)) =
        cocodeCoords.κ (pairVec 0 1) := by
      rw [rho11_pairVec]
      rcases hσ'.2 with ⟨h0, h1⟩ | ⟨h0, h1⟩
      · rw [h0, h1]
      · rw [h0, h1, pairVec, pairVec, mul_comm]
    rw [kappa11_pairVec_zero_one] at key
    exact key

theorem perfectCore_img10_mog21
    : perfectCore (img10 mog21) = img10 mog21 := by
  have := finite_mulAut W10
  rw [img10, perfectCore_map_subgroupOf mog21_le_mog22plus,
    perfectCore_eq_self_of_perfect commutator_mog21]

theorem perfectCore_img11_mog22
    : perfectCore (img11 mog22) = img11 mog22 := by
  have := finite_mulAut W11
  rw [img11, perfectCore_map_subgroupOf (inf_le_left.trans inf_le_left),
    perfectCore_eq_self_of_perfect commutator_mog22]

theorem perfectCore_img11_mog22plus
    : perfectCore (img11 mog22plus) = img11 mog22 := by
  have := finite_mulAut W11
  rw [img11, perfectCore_map_subgroupOf inf_le_left, perfectCore_mog22plus, img11]

theorem isSimpleGroup_img10_mog21
    : IsSimpleGroup ↥(img10 mog21) := by
  have := isSimpleGroup_mog21
  exact (((mog21.subgroupOf mog22plus).equivMapOfInjective _
    rho10_mog22plus_injective).symm.trans
      (Subgroup.subgroupOfEquivOfLe mog21_le_mog22plus)).isSimpleGroup

theorem card_img10_mog21
    : Nat.card ↥(img10 mog21) = 20160 := by
  rw [img10, Subgroup.card_map_of_injective rho10_mog22plus_injective,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe mog21_le_mog22plus).toEquiv, card_mog21]

theorem isSimpleGroup_img11_mog22
    : IsSimpleGroup ↥(img11 mog22) := by
  have := isSimpleGroup_mog22
  exact (((mog22.subgroupOf AutPerm).equivMapOfInjective _
    (rho11_injective AutPerm le_rfl)).symm.trans
      (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans inf_le_left))).isSimpleGroup

theorem card_img11_mog22
    : Nat.card ↥(img11 mog22) = 443520 := by
  rw [img11, Subgroup.card_map_of_injective (rho11_injective AutPerm le_rfl),
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans inf_le_left)).toEquiv,
    card_mog22]

theorem o2Data_std10
    : O2Data (img10 mog22) (toW 10 48) 20160 :=
  O2Data.of_eq ((congrArg perfectCore stabV_img10_mog22).trans perfectCore_img10_mog21)
    isSimpleGroup_img10_mog21 card_img10_mog21 commV_img10_mog21 centralizer_img10_mog21

theorem o2Data_std11_23
    : O2Data (img11 mog23) (toW 11 95) 443520 :=
  O2Data.of_eq ((congrArg perfectCore stabV_img11_mog23).trans perfectCore_img11_mog22)
    isSimpleGroup_img11_mog22 card_img11_mog22 commV_img11_mog22 centralizer_img11_mog22

theorem o2Data_std11_24
    : O2Data (img11 AutPerm) (toW 11 95) 443520 :=
  O2Data.of_eq ((congrArg perfectCore stabV_img11_autPerm).trans perfectCore_img11_mog22plus)
    isSimpleGroup_img11_mog22 card_img11_mog22 commV_img11_mog22 centralizer_img11_mog22

section Transport

variable {numer denom : Subgroup (G6.PermMod 24)} {W : Type*} [CommGroup W]
  {V : Type*} [CommGroup V]

theorem SecCoords.exists_map_eq_of_realizesBy (c : SecCoords numer denom W)
    {Γ : Subgroup (Equiv.Perm (Fin 24))} (hΓ : ∀ σ ∈ Γ, Preserves numer denom σ)
    {H : Subgroup (MulAut V)} {π : (FFModel.golaySec Γ numer denom).Gam →* ↥H}
    {β : ↥(⊤ : Subgroup V) →* ↥numer ⧸ denom.subgroupOf numer}
    (hb : RealizesBy (FFModel.golaySec Γ numer denom) H ⊤ ⊥ π β) :
    ∃ e : V ≃* W, H.map (congrHom e) = (c.rho Γ hΓ).range ∧
      ∀ (v : V) (m : ↥numer), β ⟨v, Subgroup.mem_top v⟩ = QuotientGroup.mk m ↔
        e v = c.κ m := by
  have hb' := hb
  obtain ⟨-, -, -, -, -, -, -, hβs, hβ1, hβa⟩ := hb'
  obtain ⟨e, he, hcompat⟩ := c.exists_equiv_compat hΓ (fun γ => ((π γ : ↥H) : MulAut V)) β hβs
    (fun v hv => Subgroup.mem_bot.1 ((hβ1 _).1 hv))
    (fun γ v m hm => hβa γ ⟨v, Subgroup.mem_top v⟩ m (Subgroup.mem_top _) _ hm)
  refine ⟨e, ?_, hcompat⟩
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

end Transport

variable {V : Type*} [CommGroup V] {L : Subgroup (MulAut V)}

theorem card_of_cocode22
    (h : MathieuCocode22 L ⊤ ⊥) : Nat.card V = 2 ^ 10 := by
  obtain ⟨e, -⟩ := cocode22_std h
  rw [Nat.card_congr e.toEquiv]; exact natCard_W10

theorem card_of_cocode23
    (h : MathieuCocode23 L ⊤ ⊥) :
    Nat.card V = 2 ^ 11 ∧ Nat.card L = 10200960 := by
  obtain ⟨e, he⟩ := cocode23_std h
  refine ⟨by rw [Nat.card_congr e.toEquiv]; exact natCard_W11, ?_⟩
  calc Nat.card L = Nat.card (L.map (congrHom e)) :=
        (Subgroup.card_map_of_injective (congrHom_injective e)).symm
    _ = Nat.card (rho11 mog23 inf_le_left).range := by rw [he]; rfl
    _ = Nat.card mog23 :=
        (Nat.card_congr (MonoidHom.ofInjective (rho11_injective mog23 inf_le_left)).toEquiv).symm
    _ = 10200960 := card_mog23

theorem card_of_cocode24
    (h : MathieuCocode24 L ⊤ ⊥) :
    Nat.card V = 2 ^ 11 ∧ Nat.card L = 244823040 := by
  obtain ⟨e, he⟩ := cocode24_std h
  refine ⟨by rw [Nat.card_congr e.toEquiv]; exact natCard_W11, ?_⟩
  calc Nat.card L = Nat.card (L.map (congrHom e)) :=
        (Subgroup.card_map_of_injective (congrHom_injective e)).symm
    _ = Nat.card (rho11 AutPerm le_rfl).range := by rw [he]; rfl
    _ = Nat.card AutPerm :=
        (Nat.card_congr (MonoidHom.ofInjective (rho11_injective AutPerm le_rfl)).toEquiv).symm
    _ = 244823040 := card_AutPerm

theorem cocode22_o2_std
    (h : MathieuCocode22 L ⊤ ⊥) {v : V} (hv : IsCocodeO2 L v) :
    ∃ e : V ≃* W10, L.map (congrHom e) = img10 mog22 ∧ e v = toW 10 48 := by
  have hcard := card_of_cocode22 h
  rcases hv with ⟨π, β, hRB, -⟩ | ⟨x, π, β, hRB, -⟩ | ⟨x, y, hxy, π, β, hRB, j, hxj, hyj, hβ⟩
  · have := (card_of_cocode24 ((realizes_iff _ _ _ _).2 ⟨π, β, hRB⟩)).1
    rw [hcard] at this
    norm_num at this
  · have := (card_of_cocode23 ⟨x, (realizes_iff _ _ _ _).2 ⟨π, β, hRB⟩⟩).1
    rw [hcard] at this
    norm_num at this
  obtain ⟨z, hzx, hzy, hzj⟩ : ∃ z : Fin 24, z ≠ x ∧ z ≠ y ∧ z ≠ j := by
    by_contra hc
    push Not at hc
    have : ∀ z : Fin 24, z = x ∨ z = y ∨ z = j := fun z => by
      by_cases h1 : z = x
      · exact Or.inl h1
      · by_cases h2 : z = y
        · exact Or.inr (Or.inl h2)
        · exact Or.inr (Or.inr (hc z h1 h2))
    have hcard3 : (Finset.univ : Finset (Fin 24)).card ≤ ({x, y, j} : Finset (Fin 24)).card :=
      Finset.card_le_card fun z _ => by
        rcases this z with rfl | rfl | rfl <;> simp
    have := hcard3.trans Finset.card_le_three
    simp at this
  obtain ⟨τ, hτ, hτ0, hτ1, hτ2, -⟩ := CFSG.Monster.B.TwoA.autPerm_maps_four x y j z hxy hxj
    (Ne.symm hzx) hyj (Ne.symm hzy) (Ne.symm hzj)
  obtain ⟨hn, hC⟩ := preserves_iff_of_mem hτ
  have hτ0' : τ⁻¹ x = 0 := by rw [← hτ0]; simp
  have hτ1' : τ⁻¹ y = 1 := by rw [← hτ1]; simp
  have hτ2' : τ⁻¹ j = 2 := by rw [← hτ2]; simp
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
  obtain ⟨e, he, hcompat⟩ := (cocode22Coords.conj τ hn hd).exists_map_eq_of_realizesBy hΓxy hRB
  refine ⟨e, ?_, ?_⟩
  · rw [he, ← range_rho10_eq_img10 mog22 mog22_le_mog22plus]
    refine cocode22Coords.range_rho_conj τ hn hd _ hΓxy fun σ => ?_
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
  · have hκ : (cocode22Coords.conj τ hn hd).κ (pairVec x j) = toW 10 48 := by
      change cocode22Coords.κ (G6.permAct 24 τ⁻¹ (pairVec x j)) = toW 10 48
      rw [permAct_pairVec, hτ0', hτ2', kappa22_pairVec_zero_two]
    exact ((hcompat v ⟨pairVec x j, pairVec_mem_coreMod _ _⟩).1 hβ).trans hκ

theorem cocode23_o2_std
    (h : MathieuCocode23 L ⊤ ⊥) {v : V} (hv : IsCocodeO2 L v) :
    ∃ e : V ≃* W11, L.map (congrHom e) = img11 mog23 ∧ e v = toW 11 95 := by
  have hcard := card_of_cocode23 h
  rcases hv with ⟨π, β, hRB, -⟩ | ⟨x, π, β, hRB, j, hxj, hβ⟩ | ⟨x, y, hxy, π, β, hRB, -⟩
  · have := (card_of_cocode24 ((realizes_iff _ _ _ _).2 ⟨π, β, hRB⟩)).2
    rw [hcard.2] at this
    norm_num at this
  swap
  · have := card_of_cocode22 ⟨x, y, hxy, (realizes_iff _ _ _ _).2 ⟨π, β, hRB⟩⟩
    rw [hcard.1] at this
    norm_num at this
  obtain ⟨τ, hτ, hτ0, hτ1⟩ := CFSG.Monster.B.TwoA.autPerm_maps_two x j hxj
  obtain ⟨hn, hd⟩ := preserves_iff_of_mem hτ
  have hΓx : ∀ σ ∈ AutPerm ⊓ stab x, Preserves (G6.coreMod 24) golayC σ :=
    fun _ hσ => preserves_cocode hσ.1
  have hτ0' : τ⁻¹ x = 0 := by rw [← hτ0]; simp
  have hτ1' : τ⁻¹ j = 1 := by rw [← hτ1]; simp
  obtain ⟨e, he, hcompat⟩ := (cocodeCoords.conj τ hn hd).exists_map_eq_of_realizesBy hΓx hRB
  refine ⟨e, ?_, ?_⟩
  · rw [he, ← range_rho11_eq_img11 mog23 inf_le_left]
    refine cocodeCoords.range_rho_conj τ hn hd _ hΓx fun σ => ?_
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
  · have hκ : (cocodeCoords.conj τ hn hd).κ (pairVec x j) = toW 11 95 := by
      change cocodeCoords.κ (G6.permAct 24 τ⁻¹ (pairVec x j)) = toW 11 95
      rw [permAct_pairVec, hτ0', hτ1', kappa11_pairVec_zero_one]
    exact ((hcompat v ⟨pairVec x j, pairVec_mem_coreMod _ _⟩).1 hβ).trans hκ

theorem cocode24_o2_std
    (h : MathieuCocode24 L ⊤ ⊥) {v : V} (hv : IsCocodeO2 L v) :
    ∃ e : V ≃* W11, L.map (congrHom e) = img11 AutPerm ∧ e v = toW 11 95 := by
  have hcard := card_of_cocode24 h
  rcases hv with ⟨π, β, hRB, i, j, hij, hβ⟩ | ⟨x, π, β, hRB, -⟩ | ⟨x, y, hxy, π, β, hRB, -⟩
  rotate_left
  · have := (card_of_cocode23 ⟨x, (realizes_iff _ _ _ _).2 ⟨π, β, hRB⟩⟩).2
    rw [hcard.2] at this
    norm_num at this
  · have := card_of_cocode22 ⟨x, y, hxy, (realizes_iff _ _ _ _).2 ⟨π, β, hRB⟩⟩
    rw [hcard.1] at this
    norm_num at this
  obtain ⟨τ, hτ, hτ0, hτ1⟩ := CFSG.Monster.B.TwoA.autPerm_maps_two i j hij
  obtain ⟨hn, hd⟩ := preserves_iff_of_mem hτ
  have hΓ : ∀ σ ∈ AutPerm, Preserves (G6.coreMod 24) golayC σ := fun _ hσ => preserves_cocode hσ
  have hτ0' : τ⁻¹ i = 0 := by rw [← hτ0]; simp
  have hτ1' : τ⁻¹ j = 1 := by rw [← hτ1]; simp
  obtain ⟨e, he, hcompat⟩ := (cocodeCoords.conj τ hn hd).exists_map_eq_of_realizesBy hΓ hRB
  refine ⟨e, ?_, ?_⟩
  · rw [he, ← range_rho11_eq_img11 AutPerm le_rfl]
    refine cocodeCoords.range_rho_conj τ hn hd _ hΓ fun σ => ?_
    constructor
    · intro hσ
      exact AutPerm.mul_mem (AutPerm.mul_mem (AutPerm.inv_mem hτ) hσ) hτ
    · intro hσ
      have := AutPerm.mul_mem (AutPerm.mul_mem hτ hσ) (AutPerm.inv_mem hτ)
      simpa [mul_assoc] using this
  · have hκ : (cocodeCoords.conj τ hn hd).κ (pairVec i j) = toW 11 95 := by
      change cocodeCoords.κ (G6.permAct 24 τ⁻¹ (pairVec i j)) = toW 11 95
      rw [permAct_pairVec, hτ0', hτ1', kappa11_pairVec_zero_one]
    exact ((hcompat v ⟨pairVec i j, pairVec_mem_coreMod _ _⟩).1 hβ).trans hκ

theorem o2Data_of_cocode22
    (h : MathieuCocode22 L ⊤ ⊥) {v : V} (hv : IsCocodeO2 L v) :
    O2Data L v 20160 := by
  have : Finite V := Nat.finite_of_card_ne_zero (by rw [card_of_cocode22 h]; norm_num)
  obtain ⟨e, he, hev⟩ := cocode22_o2_std h hv
  exact O2Data.of_map' e he hev o2Data_std10

theorem o2Data_of_cocode23
    (h : MathieuCocode23 L ⊤ ⊥) {v : V} (hv : IsCocodeO2 L v) :
    O2Data L v 443520 := by
  have : Finite V := Nat.finite_of_card_ne_zero (by rw [(card_of_cocode23 h).1]; norm_num)
  obtain ⟨e, he, hev⟩ := cocode23_o2_std h hv
  exact O2Data.of_map' e he hev o2Data_std11_23

theorem o2Data_of_cocode24
    (h : MathieuCocode24 L ⊤ ⊥) {v : V} (hv : IsCocodeO2 L v) :
    O2Data L v 443520 := by
  have : Finite V := Nat.finite_of_card_ne_zero (by rw [(card_of_cocode24 h).1]; norm_num)
  obtain ⟨e, he, hev⟩ := cocode24_o2_std h hv
  exact O2Data.of_map' e he hev o2Data_std11_24

end CFSG.Quasithin.H.Mathieu
