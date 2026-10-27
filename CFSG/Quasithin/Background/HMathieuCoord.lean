module

public import CFSG.Quasithin.Background.HMathieuStatements
public import CFSG.Quasithin.Background.HTransport

public section

namespace CFSG.Quasithin.H.Mathieu

open CFSG.Monster.Code

section Generic

variable (numer denom : Subgroup (G6.PermMod 24)) (W : Type*) [CommGroup W]

structure SecCoords where
  κ : G6.PermMod 24 →* W
  lift : W →* G6.PermMod 24
  lift_mem : ∀ w, lift w ∈ numer
  κ_lift : ∀ w, κ (lift w) = w
  ker_iff : ∀ m ∈ numer, κ m = 1 ↔ m ∈ denom

variable {numer denom W}

@[expose] def Preserves (numer denom : Subgroup (G6.PermMod 24)) (σ : Equiv.Perm (Fin 24)) :
    Prop :=
  (∀ m ∈ numer, G6.permAct 24 σ m ∈ numer) ∧ (∀ m ∈ denom, G6.permAct 24 σ m ∈ denom)

namespace SecCoords

variable (c : SecCoords numer denom W)

@[expose] def rhoHom (σ : Equiv.Perm (Fin 24)) : W →* W :=
  c.κ.comp ((G6.permAct 24 σ).toMonoidHom.comp c.lift)

theorem rhoHom_apply (σ : Equiv.Perm (Fin 24)) (w : W) :
    c.rhoHom σ w = c.κ (G6.permAct 24 σ (c.lift w)) := rfl

theorem mul_lift_inv_mem {m : G6.PermMod 24} (hm : m ∈ numer) :
    m * (c.lift (c.κ m))⁻¹ ∈ denom := by
  refine (c.ker_iff _ (numer.mul_mem hm (numer.inv_mem (c.lift_mem _)))).1 ?_
  rw [map_mul, map_inv, c.κ_lift, mul_inv_cancel]

theorem κ_permAct {σ : Equiv.Perm (Fin 24)} (hσ : Preserves numer denom σ)
    {m : G6.PermMod 24} (hm : m ∈ numer) :
    c.κ (G6.permAct 24 σ m) = c.rhoHom σ (c.κ m) := by
  rw [rhoHom_apply]
  have hd := c.mul_lift_inv_mem hm
  have hmd : m = (m * (c.lift (c.κ m))⁻¹) * c.lift (c.κ m) := (inv_mul_cancel_right m _).symm
  have h3 : G6.permAct 24 σ (m * (c.lift (c.κ m))⁻¹) ∈ numer :=
    hσ.1 _ (numer.mul_mem hm (numer.inv_mem (c.lift_mem _)))
  have h4 : c.κ (G6.permAct 24 σ (m * (c.lift (c.κ m))⁻¹)) = 1 :=
    (c.ker_iff _ h3).2 (hσ.2 _ hd)
  conv_lhs => rw [hmd, map_mul, map_mul, h4, one_mul]

theorem rhoHom_mul {σ τ : Equiv.Perm (Fin 24)} (hσ : Preserves numer denom σ)
    (hτ : Preserves numer denom τ) (w : W) :
    c.rhoHom (σ * τ) w = c.rhoHom σ (c.rhoHom τ w) := by
  rw [rhoHom_apply, map_mul, MulAut.mul_apply, c.κ_permAct hσ (hτ.1 _ (c.lift_mem w))]
  rfl

theorem rhoHom_one (w : W) : c.rhoHom 1 w = w := by
  rw [rhoHom_apply, map_one, MulAut.one_apply, c.κ_lift]

variable (Γ : Subgroup (Equiv.Perm (Fin 24))) (hΓ : ∀ σ ∈ Γ, Preserves numer denom σ)

@[expose] def rho : ↥Γ →* MulAut W where
  toFun σ :=
    { toFun := c.rhoHom σ
      invFun := c.rhoHom (σ⁻¹ : ↥Γ)
      left_inv := fun w => by
        rw [← c.rhoHom_mul (hΓ _ (σ⁻¹ : ↥Γ).2) (hΓ _ σ.2), ← Subgroup.coe_mul, inv_mul_cancel,
          Subgroup.coe_one, c.rhoHom_one]
      right_inv := fun w => by
        rw [← c.rhoHom_mul (hΓ _ σ.2) (hΓ _ (σ⁻¹ : ↥Γ).2), ← Subgroup.coe_mul, mul_inv_cancel,
          Subgroup.coe_one, c.rhoHom_one]
      map_mul' := map_mul (c.rhoHom σ) }
  map_one' := by
    ext w
    exact c.rhoHom_one w
  map_mul' σ τ := by
    ext w
    exact c.rhoHom_mul (hΓ _ σ.2) (hΓ _ τ.2) w

theorem rho_apply (σ : ↥Γ) (w : W) : c.rho Γ hΓ σ w = c.κ (G6.permAct 24 σ (c.lift w)) := rfl

theorem κ_permAct_rho (σ : ↥Γ) {m : G6.PermMod 24} (hm : m ∈ numer) :
    c.κ (G6.permAct 24 σ m) = c.rho Γ hΓ σ (c.κ m) :=
  c.κ_permAct (hΓ _ σ.2) hm

end SecCoords

variable {V : Type*} [CommGroup V]

theorem SecCoords.exists_equiv_core (c : SecCoords numer denom W)
    {Γ : Subgroup (Equiv.Perm (Fin 24))} (hΓ : ∀ σ ∈ Γ, Preserves numer denom σ)
    (π : ↥Γ → MulAut V) (β : ↥(⊤ : Subgroup V) →* ↥numer ⧸ denom.subgroupOf numer)
    (hβs : ∀ q, ∃ u, β u = q) (hβ1 : ∀ v : V, β ⟨v, Subgroup.mem_top v⟩ = 1 → v = 1)
    (hβa : ∀ (γ : ↥Γ) (v : V) (m : ↥numer), β ⟨v, Subgroup.mem_top v⟩ = QuotientGroup.mk m →
      β ⟨π γ v, Subgroup.mem_top _⟩ =
        QuotientGroup.mk ⟨G6.permAct 24 γ m, (hΓ γ γ.2).1 m m.2⟩) :
    ∃ e : V ≃* W, ∀ (γ : ↥Γ) (v : V), e (π γ v) = c.rho Γ hΓ γ (e v) := by
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
  refine ⟨MulEquiv.ofBijective e₀ hbij, fun γ v => ?_⟩
  rw [MulEquiv.ofBijective_apply, MulEquiv.ofBijective_apply]
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β ⟨v, Subgroup.mem_top v⟩)
  rw [he₀, he₀, hβa γ v m hm.symm, hκb, ← hm, hκb]
  exact c.κ_permAct_rho Γ hΓ γ m.2

theorem SecCoords.exists_equiv (c : SecCoords numer denom W) {Γ : Subgroup (Equiv.Perm (Fin 24))}
    (hΓ : ∀ σ ∈ Γ, Preserves numer denom σ) {H : Subgroup (MulAut V)}
    {π : (FFModel.golaySec Γ numer denom).Gam →* ↥H}
    {β : ↥(⊤ : Subgroup V) →* ↥numer ⧸ denom.subgroupOf numer}
    (h : RealizesBy (FFModel.golaySec Γ numer denom) H ⊤ ⊥ π β) :
    ∃ e : V ≃* W, ∀ (γ : ↥Γ) (v : V), e (((π γ : ↥H) : MulAut V) v) = c.rho Γ hΓ γ (e v) := by
  obtain ⟨-, -, -, -, -, -, -, hβs, hβ1, hβa⟩ := h
  exact c.exists_equiv_core hΓ (fun γ => ((π γ : ↥H) : MulAut V)) β hβs
    (fun v hv => Subgroup.mem_bot.1 ((hβ1 _).1 hv))
    (fun γ v m hm => hβa γ ⟨v, Subgroup.mem_top v⟩ m (Subgroup.mem_top _) _ hm)

theorem SecCoords.exists_map_eq (c : SecCoords numer denom W) {Γ : Subgroup (Equiv.Perm (Fin 24))}
    (hΓ : ∀ σ ∈ Γ, Preserves numer denom σ) {H : Subgroup (MulAut V)}
    (h : (FFModel.golaySec Γ numer denom).Realizes H ⊤ ⊥) :
    ∃ e : V ≃* W, H.map (congrHom e) = (c.rho Γ hΓ).range := by
  obtain ⟨π, β, hb⟩ := (realizes_iff _ _ _ _).1 h
  obtain ⟨e, he⟩ := c.exists_equiv hΓ hb
  have hπ : ∀ γ : ↥Γ, congrHom e ((π γ : ↥H) : MulAut V) = c.rho Γ hΓ γ := by
    intro γ
    ext w
    rw [congrHom_apply, he, MulEquiv.apply_symm_apply]
  refine ⟨e, le_antisymm ?_ ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨γ, hγ⟩ := hb.1 ⟨x, hx⟩
    refine ⟨γ, ?_⟩
    have h1 := hπ γ
    rw [hγ] at h1
    exact h1.symm
  · rintro _ ⟨γ, rfl⟩
    exact ⟨_, (π γ).2, hπ γ⟩

end Generic

section Syndrome

@[expose] def bMat : Matrix (Fin 12) (Fin 24) (ZMod 2) := Matrix.of fun i k => B i k

@[expose] def synd : (Fin 24 → ZMod 2) →ₗ[ZMod 2] (Fin 12 → ZMod 2) := bMat.mulVecLin

@[expose] def Dmask (i : ℕ) : ℕ :=
  [0x111110, 0x111101, 0x111011, 0x110111, 0x101111, 0x11111, 0x6ca000, 0xa6c000, 0xc6a000,
    0x6ac000, 0xaaa000, 0xccc000].getD i 0

@[expose] def dW (i : Fin 12) : Fin 24 → ZMod 2 := bvec 24 (Dmask i)

@[expose] def combMap : (Fin 24 → ZMod 2) →ₗ[ZMod 2] (Fin 24 → ZMod 2) :=
  ∑ i : Fin 12, ((LinearMap.proj i).comp ψ).smulRight (B i) +
    ∑ i : Fin 12, ((LinearMap.proj i).comp synd).smulRight (dW i)

theorem combMap_apply (x : Fin 24 → ZMod 2) :
    combMap x = ∑ i, ψ x i • B i + ∑ i, synd x i • dW i := by
  simp [combMap]

private theorem combMap_single : ∀ (k : Fin 24) (c : ZMod 2),
    combMap (Pi.single k c) = Pi.single k c := by
  decide +kernel

theorem eq_comb_synd (x : Fin 24 → ZMod 2) :
    x = ∑ i, ψ x i • B i + ∑ i, synd x i • dW i := by
  rw [← combMap_apply]
  have h : combMap = LinearMap.id := LinearMap.pi_ext fun k c => combMap_single k c
  rw [h, LinearMap.id_apply]

private theorem synd_B : ∀ j : Fin 12, synd (B j) = 0 := by decide

theorem synd_eq_zero_of_mem {x : Fin 24 → ZMod 2} (hx : x ∈ C) : synd x = 0 := by
  rw [eq_comb_of_mem_C hx, map_sum]
  simp [synd_B]

theorem synd_eq_zero_iff (x : Fin 24 → ZMod 2) : synd x = 0 ↔ x ∈ C := by
  refine ⟨fun h => ?_, synd_eq_zero_of_mem⟩
  rw [eq_comb_synd x, h]
  simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero]
  exact C.sum_mem fun i _ => C.smul_mem _ (B_mem_C i)

private theorem sum_B_six : ∀ k : Fin 24, ∑ i : Fin 6, B (Fin.castLE (by norm_num) i) k = 1 := by
  decide

theorem synd_parity (x : Fin 24 → ZMod 2) :
    ∑ i : Fin 6, synd x (Fin.castLE (by norm_num) i) = ∑ k, x k := by
  simp only [synd, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, bMat, Matrix.of_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_mul, sum_B_six, one_mul]

end Syndrome

section Cocode

@[expose] def emb11 (j : Fin 11) : Fin 12 :=
  if h : (j : ℕ) < 5 then ⟨j, by omega⟩ else ⟨j + 1, by omega⟩

@[expose] def ccE : (Fin 24 → ZMod 2) →ₗ[ZMod 2] (Fin 11 → ZMod 2) :=
  LinearMap.pi fun j => (LinearMap.proj (emb11 j)).comp synd

@[expose] def Umask (j : ℕ) : ℕ :=
  [0x100001, 0x100010, 0x100100, 0x101000, 0x110000, 0x6ca000, 0xa6c000, 0xc6a000, 0x6ac000,
    0xaaa000, 0xccc000].getD j 0

@[expose] def uW (j : Fin 11) : Fin 24 → ZMod 2 := bvec 24 (Umask j)

@[expose] def liftE : (Fin 11 → ZMod 2) →ₗ[ZMod 2] (Fin 24 → ZMod 2) :=
  ∑ j : Fin 11, (LinearMap.proj j).smulRight (uW j)

theorem liftE_apply (t : Fin 11 → ZMod 2) : liftE t = ∑ j, t j • uW j := by
  simp [liftE]

private theorem ccE_uW : ∀ j : Fin 11, ccE (uW j) = Pi.single j 1 := by decide

private theorem sum_uW : ∀ j : Fin 11, ∑ k, uW j k = 0 := by decide

theorem ccE_liftE (t : Fin 11 → ZMod 2) : ccE (liftE t) = t := by
  rw [liftE_apply, map_sum]
  simp only [map_smul, ccE_uW]
  funext j
  simp [Finset.sum_apply, Pi.single_apply]

theorem sum_liftE (t : Fin 11 → ZMod 2) : ∑ k, liftE t k = 0 := by
  rw [liftE_apply]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  simp [← Finset.mul_sum, sum_uW]

theorem eq_zero_of_emb11 (s : Fin 12 → ZMod 2) (h : ∀ j : Fin 11, s (emb11 j) = 0)
    (hp : ∑ i : Fin 6, s (Fin.castLE (by norm_num) i) = 0) : s = 0 := by
  have h0 : s 0 = 0 := h 0
  have h1 : s 1 = 0 := h 1
  have h2 : s 2 = 0 := h 2
  have h3 : s 3 = 0 := h 3
  have h4 : s 4 = 0 := h 4
  have h6 : s 6 = 0 := h 5
  have h7 : s 7 = 0 := h 6
  have h8 : s 8 = 0 := h 7
  have h9 : s 9 = 0 := h 8
  have h10 : s 10 = 0 := h 9
  have h11 : s 11 = 0 := h 10
  have h5 : s 5 = 0 := by
    have hsum : ∑ i : Fin 6, s (Fin.castLE (by norm_num) i) =
        s 0 + s 1 + s 2 + s 3 + s 4 + s 5 := by
      rw [Fin.sum_univ_six]
      rfl
    rw [hsum, h0, h1, h2, h3, h4] at hp
    simpa using hp
  funext i
  fin_cases i <;> assumption

theorem ccE_eq_zero_iff {x : Fin 24 → ZMod 2} (hx : ∑ k, x k = 0) : ccE x = 0 ↔ x ∈ C := by
  rw [← synd_eq_zero_iff]
  constructor
  · intro h
    refine eq_zero_of_emb11 _ (fun j => congrFun h j) ?_
    rw [synd_parity, hx]
  · intro h
    funext j
    show synd x (emb11 j) = 0
    rw [h]
    rfl

end Cocode

section Conj

variable {numer denom numer' denom' : Subgroup (G6.PermMod 24)} {W : Type*} [CommGroup W]

theorem permAct_inv_apply_permAct (τ : Equiv.Perm (Fin 24)) (m : G6.PermMod 24) :
    G6.permAct 24 τ⁻¹ (G6.permAct 24 τ m) = m := by
  rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]

@[expose] def SecCoords.conj (c : SecCoords numer denom W) (τ : Equiv.Perm (Fin 24))
    (hn : ∀ m, m ∈ numer' ↔ G6.permAct 24 τ⁻¹ m ∈ numer)
    (hd : ∀ m, m ∈ denom' ↔ G6.permAct 24 τ⁻¹ m ∈ denom) : SecCoords numer' denom' W where
  κ := c.κ.comp (G6.permAct 24 τ⁻¹).toMonoidHom
  lift := (G6.permAct 24 τ).toMonoidHom.comp c.lift
  lift_mem w := by
    rw [hn]
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply]
    rw [permAct_inv_apply_permAct]
    exact c.lift_mem w
  κ_lift w := by
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply]
    rw [permAct_inv_apply_permAct, c.κ_lift]
  ker_iff m hm := by
    rw [hd]
    exact c.ker_iff _ ((hn m).1 hm)

theorem SecCoords.conj_rhoHom (c : SecCoords numer denom W) (τ : Equiv.Perm (Fin 24))
    (hn : ∀ m, m ∈ numer' ↔ G6.permAct 24 τ⁻¹ m ∈ numer)
    (hd : ∀ m, m ∈ denom' ↔ G6.permAct 24 τ⁻¹ m ∈ denom) (σ : Equiv.Perm (Fin 24)) :
    (c.conj τ hn hd).rhoHom σ = c.rhoHom (τ⁻¹ * σ * τ) := by
  ext w
  simp only [SecCoords.rhoHom_apply, SecCoords.conj, MonoidHom.coe_comp,
    MulEquiv.coe_toMonoidHom, Function.comp_apply]
  rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← map_mul, ← map_mul, mul_assoc]

theorem SecCoords.range_rho_conj (c : SecCoords numer denom W) (τ : Equiv.Perm (Fin 24))
    (hn : ∀ m, m ∈ numer' ↔ G6.permAct 24 τ⁻¹ m ∈ numer)
    (hd : ∀ m, m ∈ denom' ↔ G6.permAct 24 τ⁻¹ m ∈ denom)
    {Γ Γ' : Subgroup (Equiv.Perm (Fin 24))} (hΓ : ∀ σ ∈ Γ, Preserves numer denom σ)
    (hΓ' : ∀ σ ∈ Γ', Preserves numer' denom' σ) (hΓΓ' : ∀ σ, σ ∈ Γ' ↔ τ⁻¹ * σ * τ ∈ Γ) :
    ((c.conj τ hn hd).rho Γ' hΓ').range = (c.rho Γ hΓ).range := by
  apply le_antisymm
  · rintro _ ⟨σ, rfl⟩
    refine ⟨⟨τ⁻¹ * σ * τ, (hΓΓ' σ).1 σ.2⟩, ?_⟩
    ext w
    show c.rhoHom (τ⁻¹ * σ * τ) w = (c.conj τ hn hd).rhoHom σ w
    rw [c.conj_rhoHom]
  · rintro _ ⟨σ, rfl⟩
    have hσ : τ * σ * τ⁻¹ ∈ Γ' := by
      rw [hΓΓ']
      simp [mul_assoc]
    refine ⟨⟨τ * σ * τ⁻¹, hσ⟩, ?_⟩
    ext w
    show (c.conj τ hn hd).rhoHom (τ * σ * τ⁻¹) w = c.rhoHom σ w
    rw [c.conj_rhoHom]
    congr 2
    group

end Conj

section CocodeSec

theorem mem_golayC_iff (m : G6.PermMod 24) : m ∈ golayC ↔ Multiplicative.toAdd m ∈ C := Iff.rfl

theorem mem_coreMod_iff (m : G6.PermMod 24) :
    m ∈ G6.coreMod 24 ↔ ∑ k, Multiplicative.toAdd m k = 0 := Iff.rfl

theorem toAdd_permAct (σ : Equiv.Perm (Fin 24)) (m : G6.PermMod 24) :
    Multiplicative.toAdd (G6.permAct 24 σ m) = permWord σ (Multiplicative.toAdd m) := rfl

@[expose] def cocodeCoords :
    SecCoords (G6.coreMod 24) golayC (Multiplicative (Fin 11 → ZMod 2)) where
  κ := AddMonoidHom.toMultiplicative ccE.toAddMonoidHom
  lift := AddMonoidHom.toMultiplicative liftE.toAddMonoidHom
  lift_mem w := sum_liftE (Multiplicative.toAdd w)
  κ_lift w := by
    change Multiplicative.ofAdd (ccE (liftE (Multiplicative.toAdd w))) = w
    rw [ccE_liftE]
    rfl
  ker_iff m hm := by
    change Multiplicative.ofAdd (ccE (Multiplicative.toAdd m)) = 1 ↔ _
    rw [mem_golayC_iff, ← ccE_eq_zero_iff hm]
    exact ⟨fun h => congrArg Multiplicative.toAdd h, fun h => congrArg Multiplicative.ofAdd h⟩

theorem sum_permWord (σ : Equiv.Perm (Fin 24)) (x : Fin 24 → ZMod 2) :
    ∑ k, permWord σ x k = ∑ k, x k :=
  Equiv.sum_comp σ⁻¹ x

theorem preserves_cocode {σ : Equiv.Perm (Fin 24)} (hσ : σ ∈ AutPerm) :
    Preserves (G6.coreMod 24) golayC σ := by
  refine ⟨fun m hm => ?_, fun m hm => ?_⟩
  · rw [mem_coreMod_iff, toAdd_permAct, sum_permWord]
    exact hm
  · rw [mem_golayC_iff, toAdd_permAct]
    exact permWord_mem_of_mem_AutPerm hσ hm

end CocodeSec

end CFSG.Quasithin.H.Mathieu
