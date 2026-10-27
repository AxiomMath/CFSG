module

public import CFSG.Quasithin.Vol2.Ch10SecD31C
public import CFSG.Quasithin.Background.B4L3Two

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Quasithin

variable {W : Type*} [CommGroup W] {Gr : Subgroup (MulAut W)}

theorem mem_of_normalizes (D : L3Data Gr ⊤ (fixV Gr)) (hcomm : commV Gr = ⊤) {x : MulAut W}
    (hx : ∀ g, g ∈ Gr ↔ x * g * x⁻¹ ∈ Gr) : x ∈ Gr := by
  have hxZ : ∀ z ∈ fixV Gr, x z ∈ fixV Gr := by
    intro z hz g hg
    have hg' : x⁻¹ * g * x ∈ Gr := by
      rw [hx]
      simpa [mul_assoc] using hg
    have h1 := hz _ hg'
    calc g (x z) = x ((x⁻¹ * g * x) z) := by simp [MulAut.mul_apply]
      _ = x z := by rw [h1]
  have hxZ' : ∀ z ∈ fixV Gr, x⁻¹ z ∈ fixV Gr := by
    intro z hz g hg
    have h1 := hz _ ((hx g).mp hg)
    calc g (x⁻¹ z) = x⁻¹ ((x * g * x⁻¹) z) := by simp [MulAut.mul_apply]
      _ = x⁻¹ z := by rw [h1]
  obtain ⟨δ, hδ⟩ := exists_act_of_preserves D hxZ hxZ'
  set a := D.rho δ with ha
  set u := x * a⁻¹ with hu
  have hainv : a⁻¹ = D.rho δ⁻¹ := by rw [ha, map_inv]
  have hu1 : ∀ w, bvec D (u w) = bvec D w := by
    intro w
    rw [hu, MulAut.mul_apply, hδ, hainv, bvec_rho, ← L3.act_mul, mul_inv_cancel, L3.act_one]
  have hu1i : ∀ w, bvec D (u⁻¹ w) = bvec D w := fun w => by
    have h1 := hu1 (u⁻¹ w)
    rw [MulAut.apply_inv_self] at h1
    exact h1.symm
  have hun : ∀ g ∈ Gr, u * g * u⁻¹ ∈ Gr := by
    intro g hg
    have h1 : a⁻¹ * g * a ∈ Gr :=
      Gr.mul_mem (Gr.mul_mem (Gr.inv_mem (D.rho_mem δ)) hg) (D.rho_mem δ)
    have e1 : u * g * u⁻¹ = x * (a⁻¹ * g * a) * x⁻¹ := by rw [hu]; group
    rw [e1]
    exact (hx _).mp h1
  have huc : ∀ g ∈ Gr, u * g = g * u := by
    intro g hg
    have hc : u * g * u⁻¹ * g⁻¹ ∈ Gr := Gr.mul_mem (hun g hg) (Gr.inv_mem hg)
    obtain ⟨γ, hγ⟩ := D.exists_rho hc
    obtain ⟨η, hη⟩ := D.exists_rho hg
    have hγ1 : γ = 1 := by
      apply L3.act_injective
      intro v
      obtain ⟨w, rfl⟩ := bvec_surj D v
      rw [← bvec_rho, hγ]
      have e1 : (u * g * u⁻¹ * g⁻¹) w = u (g (u⁻¹ (g⁻¹ w))) := rfl
      have hginv : g⁻¹ = D.rho η⁻¹ := by rw [← hη, map_inv]
      rw [e1, hu1, ← hη, bvec_rho, hu1i, hη, hginv, bvec_rho, ← L3.act_mul, mul_inv_cancel,
        L3.act_one]
    have h1 : u * g * u⁻¹ * g⁻¹ = 1 := by rw [← hγ, hγ1, map_one]
    calc u * g = u * g * u⁻¹ * g⁻¹ * (g * u) := by group
      _ = g * u := by rw [h1, one_mul]
  have hsub : commV Gr ≤ MonoidHom.eqLocus (u : W →* W) (MonoidHom.id W) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨g, hg, v, rfl⟩
    have hd : u v * v⁻¹ ∈ fixV Gr := by
      rw [← bvec_eq_zero_iff D, bvec_mul, bvec_inv, hu1]
      exact add_neg_cancel _
    have hgd : g (u v * v⁻¹) = u v * v⁻¹ := hd g hg
    have hug : u (g v) = g (u v) := by
      have := congrArg (fun φ : MulAut W => φ v) (huc g hg)
      exact this
    show u (g v * v⁻¹) = g v * v⁻¹
    rw [map_mul, map_inv, hug]
    have e1 : g (u v) = g (u v * v⁻¹) * g v := by rw [map_mul, map_inv]; group
    rw [e1, hgd]
    have e2 : u v = (u v * v⁻¹) * v := by group
    calc u v * v⁻¹ * g v * (u v)⁻¹ = u v * v⁻¹ * g v * ((u v * v⁻¹) * v)⁻¹ := by rw [← e2]
      _ = g v * v⁻¹ := by
        rw [mul_inv_rev, mul_inv_rev, inv_inv]
        simp only [mul_assoc, mul_left_comm, mul_comm]
        group
  have hu1' : u = 1 := by
    ext w
    have hw : w ∈ MonoidHom.eqLocus (u : W →* W) (MonoidHom.id W) :=
      hsub (hcomm ▸ Subgroup.mem_top w)
    exact hw
  have hxa : x = a := by
    rw [hu, mul_inv_eq_one] at hu1'
    exact hu1'
  rw [hxa]
  exact D.rho_mem δ

theorem isIndecompModule_of [Finite W] (D : L3Data Gr ⊤ (fixV Gr)) (hcomm : commV Gr = ⊤)
    (hcard : Nat.card W = 16) : IsIndecompModule Gr := by
  intro X Y hX hY hXY hXY'
  have hker := ker_bhom D
  have hinv : ∀ K : Subgroup W, (∀ g ∈ Gr, ∀ x ∈ K, g x ∈ K) → ∀ γ : L3.Γ,
      ∀ v ∈ K.map (bhom D), Multiplicative.ofAdd (L3.act γ (Multiplicative.toAdd v)) ∈
        K.map (bhom D) := by
    rintro K hK γ _ ⟨k, hk, rfl⟩
    refine ⟨D.rho γ k, hK _ (D.rho_mem γ) k hk, ?_⟩
    have := bvec_rho D γ k
    unfold bvec at this
    exact congrArg Multiplicative.ofAdd this
  have hcase : ∀ X Y : Subgroup W, (∀ g ∈ Gr, ∀ x ∈ X, g x ∈ X) → (∀ g ∈ Gr, ∀ y ∈ Y, g y ∈ Y) →
      X ⊓ Y = ⊥ → X ⊔ Y = ⊤ → X.map (bhom D) = ⊥ → X = ⊥ := by
    intro X Y hX hY hXY hXY' hXb
    have hXZ : X ≤ fixV Gr := by
      rw [← hker, ← Subgroup.map_eq_bot_iff]
      exact hXb
    have hYt : Y = ⊤ := by
      rw [eq_top_iff, ← hcomm]
      refine (Subgroup.closure_le _).mpr ?_
      rintro _ ⟨g, hg, v, rfl⟩
      have hv : v ∈ X ⊔ Y := hXY' ▸ Subgroup.mem_top v
      obtain ⟨x, hx, y, hy, rfl⟩ := Subgroup.mem_sup.mp hv
      have hgx : g x = x := hXZ hx g hg
      show g (x * y) * (x * y)⁻¹ ∈ Y
      rw [map_mul, hgx, mul_inv_rev]
      have e1 : x * g y * (y⁻¹ * x⁻¹) = g y * y⁻¹ := by
        calc x * g y * (y⁻¹ * x⁻¹) = x * (g y * y⁻¹) * x⁻¹ := by group
          _ = (g y * y⁻¹) * x * x⁻¹ := by rw [mul_comm x (g y * y⁻¹)]
          _ = g y * y⁻¹ := by group
      rw [e1]
      exact Y.mul_mem (hY g hg y hy) (Y.inv_mem hy)
    rw [hYt, inf_top_eq] at hXY
    exact hXY
  by_cases hXb : X.map (bhom D) = ⊥
  · exact Or.inl (hcase X Y hX hY hXY hXY' hXb)
  by_cases hYb : Y.map (bhom D) = ⊥
  · exact Or.inr (hcase Y X hY hX (by rw [inf_comm]; exact hXY) (by rw [sup_comm]; exact hXY')
      hYb)
  exfalso
  have hXt := L3.eq_top_of_invariant (hinv X hX) hXb
  have hYt := L3.eq_top_of_invariant (hinv Y hY) hYb
  have h8 : ∀ K : Subgroup W, K.map (bhom D) = ⊤ → 8 ≤ Nat.card K := by
    intro K hK
    have h1 : Nat.card ↥(K.map (bhom D)) ≤ Nat.card K :=
      Nat.card_le_card_of_surjective _ ((bhom D).subgroupMap_surjective K)
    rw [hK, Subgroup.card_top, L3Data.card_vec] at h1
    exact h1
  have hX8 := h8 X hXt
  have hY8 := h8 Y hYt
  have hinj : Function.Injective fun p : ↥X × ↥Y => (p.1 : W) * p.2 := by
    rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ ⟨⟨x', hx'⟩, ⟨y', hy'⟩⟩ h
    have h1 : x'⁻¹ * x = y' * y⁻¹ := by
      have h0 : x * y = x' * y' := h
      calc x'⁻¹ * x = x'⁻¹ * (x * y) * y⁻¹ := by group
        _ = x'⁻¹ * (x' * y') * y⁻¹ := by rw [h0]
        _ = y' * y⁻¹ := by group
    have hmem : x'⁻¹ * x ∈ X ⊓ Y :=
      ⟨X.mul_mem (X.inv_mem hx') hx, h1 ▸ Y.mul_mem hy' (Y.inv_mem hy)⟩
    rw [hXY, Subgroup.mem_bot] at hmem
    have hxx : x = x' := by
      calc x = x' * (x'⁻¹ * x) := by group
        _ = x' := by rw [hmem, mul_one]
    have hyy : y = y' := by
      have : y' * y⁻¹ = 1 := h1 ▸ hmem
      calc y = (y' * y⁻¹)⁻¹ * y' := by group
        _ = y' := by rw [this, inv_one, one_mul]
    subst hxx hyy
    rfl
  have hle := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_prod, hcard] at hle
  have := Nat.mul_le_mul hX8 hY8
  omega

theorem eq_one_of_normalizes [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    (hnat : BinaryNaturalSL Gr ⊤ (fixV Gr) 3 1) (hcard : Nat.card W = 16)
    (hcomm : commV Gr = ⊤) {x : MulAut W} (hx : ∀ g, g ∈ Gr ↔ x * g * x⁻¹ ∈ Gr)
    (hidx : (fixV (Subgroup.zpowers x)).index ≤ 2) : x = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨D⟩ := hnat.toL3Coord
  have hind := isIndecompModule_of D hcomm hcard
  obtain ⟨γ, rfl⟩ := D.exists_rho (mem_of_normalizes D hcomm hx)
  by_contra hne
  have hγ1 : γ ≠ 1 := fun h => hne (by rw [h, map_one])
  have hZ2 : Nat.card (fixV Gr) = 2 := by
    have := D.card_U
    rw [Subgroup.card_top, hcard] at this
    omega
  set S := fixV (Subgroup.zpowers (D.rho γ)) with hS
  have hSidx := Subgroup.card_mul_index S
  rw [hcard] at hSidx
  have hS4 : Nat.card S ≤ 4 := by
    by_cases hinv : L3.IsInvol γ
    · have h2 : (D.rho γ) ^ 2 = 1 := by rw [← map_pow, pow_two, hinv.1, map_one]
      obtain ⟨-, -, -, h4⟩ := B4_8_2 hW hcard hnat hind
      obtain ⟨-, hrk⟩ := h4 _ (D.rho_mem γ) hne h2
      have hp : IsPGroup 2 S :=
        IsPGroup.to_subgroup (fun w => ⟨1, by simpa using hW w⟩ : IsPGroup 2 W) S
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hp
      unfold rk at hrk
      rw [hk, padicValNat.prime_pow] at hrk
      rw [hk, hrk]
      norm_num
    · have hfix2 := L3.fixS_card_le_two γ hγ1 hinv
      have h1 := B1More.card_map_mul_card_inf_ker S (bhom D)
      have hmap : Nat.card ↥(S.map (bhom D)) ≤ 2 := by
        have hmem : ∀ m ∈ S.map (bhom D), Multiplicative.toAdd m ∈ L3.fixS γ := by
          rintro _ ⟨s, hs, rfl⟩
          have hs' : D.rho γ s = s := hs _ (Subgroup.mem_zpowers _)
          have := bvec_rho D γ s
          rw [hs'] at this
          unfold L3.fixS
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ _, this.symm⟩
        have hinj : Function.Injective fun m : ↥(S.map (bhom D)) =>
            (⟨Multiplicative.toAdd (m : Multiplicative L3.Vec), hmem _ m.2⟩ : ↥(L3.fixS γ)) := by
          intro m m' h
          simp only [Subtype.mk.injEq] at h
          exact Subtype.ext (Multiplicative.toAdd.injective h)
        have := Nat.card_le_card_of_injective _ hinj
        rw [Nat.card_eq_finsetCard] at this
        omega
      have hker' : Nat.card ↥(S ⊓ (bhom D).ker) ≤ 2 :=
        (Subgroup.card_le_of_le (inf_le_right.trans (ker_bhom D).le)).trans hZ2.le
      rw [← h1]
      calc Nat.card ↥(S.map (bhom D)) * Nat.card ↥(S ⊓ (bhom D).ker) ≤ 2 * 2 :=
            Nat.mul_le_mul hmap hker'
        _ = 4 := by norm_num
  have := Nat.mul_le_mul hS4 hidx
  omega

end CFSG.Quasithin.Vol2.Ch10.SecD
