module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08RoCloseAux3

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly


theorem ggQ2s08r4_automizer_map_conj_dvd
    {G : Type} [Group G] {Bs : Subgroup G}
     {X : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (Bs : Set G)) :
    Nat.card ↥(ggAutomizer X Bs) ∣
      Nat.card ↥(ggAutomizer (X.map (MulAut.conj g).toMonoidHom) Bs) := by
  have hle : (ggAutomizer X Bs).map (MulAut.conj (ggConjAut Bs hg)).toMonoidHom ≤
      ggAutomizer (X.map (MulAut.conj g).toMonoidHom) Bs := by
    rw [ggAutomizer_eq X Bs, ggAutomizer_eq (X.map (MulAut.conj g).toMonoidHom) Bs]
    rintro _ ⟨t, ht, rfl⟩
    exact mem_ggInduced_map_conj hg ht
  calc Nat.card ↥(ggAutomizer X Bs)
      = Nat.card ↥((ggAutomizer X Bs).map (MulAut.conj (ggConjAut Bs hg)).toMonoidHom) := by
        rw [Subgroup.card_map_of_injective (MulAut.conj (ggConjAut Bs hg)).injective]
    _ ∣ Nat.card ↥(ggAutomizer (X.map (MulAut.conj g).toMonoidHom) Bs) :=
        Subgroup.card_dvd_of_le hle

theorem ggQ2s08r4_centralizer_conj_eq'
    {G : Type} [Group G] {x : G}
    {a u w g : G}
    (hx : g * x * g⁻¹ = u) (hb : g * a * g⁻¹ = w) :
    (Subgroup.centralizer ({x, a} : Set G)).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer (Subgroup.closure ({u, w} : Set G) : Set G) := by
  have himg : (MulAut.conj g).toMonoidHom '' ({x, a} : Set G) = ({u, w} : Set G) := by
    ext z
    constructor
    · rintro ⟨t, (rfl | rfl), rfl⟩
      · exact Or.inl hx
      · exact Or.inr hb
    · rintro (rfl | rfl)
      · exact ⟨x, Or.inl rfl, hx⟩
      · exact ⟨a, Or.inr rfl, hb⟩
  calc (Subgroup.centralizer ({x, a} : Set G)).map (MulAut.conj g).toMonoidHom
      = (Subgroup.centralizer (Subgroup.closure ({x, a} : Set G) : Set G)).map
          (MulAut.conj g).toMonoidHom := by rw [Subgroup.centralizer_closure]
    _ = Subgroup.centralizer (Subgroup.map (MulAut.conj g).toMonoidHom
          (Subgroup.closure ({x, a} : Set G)) : Set G) :=
        CFSG.LocalAnalysis.ComponentInitial.conjSub_centralizer g _
    _ = Subgroup.centralizer (Subgroup.closure ({u, w} : Set G) : Set G) := by
        rw [MonoidHom.map_closure (MulAut.conj g).toMonoidHom ({x, a} : Set G), himg]

theorem ggQ2s08r4_identity
    {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
     [Finite G] (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    {B : Subgroup G} {D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) (hCav : 4 ∣ Nat.card ↥(ggAutomizer J Bs))
    (M : GGQ2LDatum 3 Bs L x) {N : ℕ} (f : Fin N → M.V) (hf : GGQ2S08ROFrame M f)
    {g : G} {φ : MulAut ↥Bs} (hInd : GGQ2Ind Bs g φ)
    (hlin : ggLin (p := 3) M.model φ = 1) :
    g ∈ Subgroup.normalizer (ggG0 3 B x L D J : Set G) := by
  have hfix : ∀ w : ↥Bs, g * (w : G) * g⁻¹ = (w : G) := fun w =>
    ggQ2s08r4_conj_eq_of_lin M hInd w w (by rw [hlin]; rfl)
  have hxfix : g * x * g⁻¹ = x := hfix ⟨x, M.hx⟩
  have hLpair : GGStdPair' 3 Bs x L := ggStdPair'_L hP hS.1 hCav
  have hLg : L.map (MulAut.conj g).toMonoidHom = L := by
    refine (ggStdPair'_unique hLB hS.1 rfl hLpair ?_).symm
    simpa only [hxfix] using ggStdPair'_conj (p := 3) hInd.1 hLpair
  have hKmem : ∀ (y : G) (K : Subgroup G), GGNbr 3 B x D J y K →
      K.map (MulAut.conj g).toMonoidHom ≤ ggG0 3 B x L D J := by
    intro y K hnbr
    have hKpair : GGStdPair' 3 Bs y K := ggStdPair'_nbr hLB hP hS.1 hCav hnbr
    have hyfix : g * y * g⁻¹ = y := hfix ⟨y, hKpair.1⟩
    have hKg : K.map (MulAut.conj g).toMonoidHom = K := by
      refine (ggStdPair'_unique hLB hS.1 rfl hKpair ?_).symm
      simpa only [hyfix] using ggStdPair'_conj (p := 3) hInd.1 hKpair
    rw [hKg]
    exact le_ggG0_of_ggNbr hnbr
  exact ggQ2s08r4_final hS hInd.1 (by rw [hLg]; exact le_ggG0_left 3 B x L D J) hKmem

theorem ggQ2s08r4_single_lin_model_x
    {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
     {N : ℕ} (M : GGQ2LDatum 3 Bs L x)
    (f : Fin N → M.V) (hf : GGQ2S08ROFrame M f) (k : Fin N) :
    ggQ2s08r4_singleEquiv M (ggQ2s08r4_basis M f hf) k
        (M.model (Additive.ofMul ⟨x, M.hx⟩)) =
      M.model (Additive.ofMul (⟨x, M.hx⟩ * ggQ2s08r4_b M f k)) := by
  rw [ggQ2s08r4_singleEquiv_apply, ggQ2s08r4_repr_model_x M f hf k]
  simp only [one_smul]
  rw [ofMul_mul, map_add, ggQ2s08r4_b_model, ggQ2s08r4_basis_apply]

theorem ggQ2s08r4_single_lin_model_b_self
    {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
     {N : ℕ} (M : GGQ2LDatum 3 Bs L x)
    (f : Fin N → M.V) (hf : GGQ2S08ROFrame M f) (k : Fin N) :
    ggQ2s08r4_singleEquiv M (ggQ2s08r4_basis M f hf) k
        (M.model (Additive.ofMul (ggQ2s08r4_b M f k))) =
      M.model (Additive.ofMul (ggQ2s08r4_b M f k)⁻¹) := by
  rw [ggQ2s08r4_b_model, ← ggQ2s08r4_basis_apply M f hf k]
  rw [ggQ2s08r4_singleEquiv_basis_self]
  rw [ofMul_inv, map_neg, ggQ2s08r4_b_model, ← ggQ2s08r4_basis_apply M f hf k]

theorem ggQ2s08r4_single_lin_model_b_ne
    {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
     {N : ℕ} (M : GGQ2LDatum 3 Bs L x)
    (f : Fin N → M.V) (hf : GGQ2S08ROFrame M f) {j k : Fin N} (hjk : j ≠ k) :
    ggQ2s08r4_singleEquiv M (ggQ2s08r4_basis M f hf) k
        (M.model (Additive.ofMul (ggQ2s08r4_b M f j))) =
      M.model (Additive.ofMul (ggQ2s08r4_b M f j)) := by
  rw [ggQ2s08r4_b_model, ← ggQ2s08r4_basis_apply M f hf j,
    ggQ2s08r4_singleEquiv_basis_of_ne M (ggQ2s08r4_basis M f hf) k j hjk]

theorem ggQ2s08r4_mul_single_lin_model_x
    {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
     {N : ℕ} (M : GGQ2LDatum 3 Bs L x)
    (f : Fin N → M.V) (hf : GGQ2S08ROFrame M f) {j k : Fin N} (hjk : j ≠ k) :
    (ggQ2s08r4_singleEquiv M (ggQ2s08r4_basis M f hf) k *
        ggQ2s08r4_singleEquiv M (ggQ2s08r4_basis M f hf) j)
        (M.model (Additive.ofMul ⟨x, M.hx⟩)) =
      M.model (Additive.ofMul (⟨x, M.hx⟩ * ggQ2s08r4_b M f k * ggQ2s08r4_b M f j)) := by
  rw [LinearEquiv.mul_apply, ggQ2s08r4_single_lin_model_x M f hf j]
  calc ggQ2s08r4_singleEquiv M (ggQ2s08r4_basis M f hf) k
        (M.model (Additive.ofMul (⟨x, M.hx⟩ * ggQ2s08r4_b M f j)))
      = ggQ2s08r4_singleEquiv M (ggQ2s08r4_basis M f hf) k
          (M.model (Additive.ofMul ⟨x, M.hx⟩) +
            M.model (Additive.ofMul (ggQ2s08r4_b M f j))) := by
        rw [ofMul_mul, map_add]
    _ = ggQ2s08r4_singleEquiv M (ggQ2s08r4_basis M f hf) k
          (M.model (Additive.ofMul ⟨x, M.hx⟩)) +
        ggQ2s08r4_singleEquiv M (ggQ2s08r4_basis M f hf) k
          (M.model (Additive.ofMul (ggQ2s08r4_b M f j))) := by
        rw [map_add]
    _ = M.model (Additive.ofMul (⟨x, M.hx⟩ * ggQ2s08r4_b M f k)) +
        M.model (Additive.ofMul (ggQ2s08r4_b M f j)) := by
        rw [ggQ2s08r4_single_lin_model_x,
          ggQ2s08r4_single_lin_model_b_ne M f hf hjk]
    _ = M.model (Additive.ofMul (⟨x, M.hx⟩ * ggQ2s08r4_b M f k * ggQ2s08r4_b M f j)) := by
        conv_rhs => rw [ofMul_mul, map_add, ggQ2s08r4_b_model]
        rw [ggQ2s08r4_b_model]

theorem ggQ2s08r4_closure_pair_mul_inv
    {G : Type} [Group G]
     (y a : G) :
    Subgroup.closure ({y, a} : Set G) = Subgroup.closure ({y * a, a⁻¹} : Set G) := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro z (hz | hz)
    · rw [hz]
      show y ∈ Subgroup.closure ({y * a, a⁻¹} : Set G)
      have h : ((y * a) * a⁻¹) ∈ Subgroup.closure ({y * a, a⁻¹} : Set G) :=
        Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inl rfl))
          (Subgroup.subset_closure (Or.inr rfl))
      rwa [mul_inv_cancel_right] at h
    · rw [hz]
      show a ∈ Subgroup.closure ({y * a, a⁻¹} : Set G)
      have h : ((a⁻¹)⁻¹) ∈ Subgroup.closure ({y * a, a⁻¹} : Set G) :=
        Subgroup.inv_mem _ (Subgroup.subset_closure (Or.inr rfl))
      rwa [inv_inv] at h
  · rw [Subgroup.closure_le]
    rintro z (hz | hz)
    · rw [hz]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inl rfl))
        (Subgroup.subset_closure (Or.inr rfl))
    · rw [hz]
      exact Subgroup.inv_mem _ (Subgroup.subset_closure (Or.inr rfl))

theorem ggQ2s08r4_sign_L_le
    {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
     [Finite G] (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    {B : Subgroup G} {D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) (hCav : 4 ∣ Nat.card ↥(ggAutomizer J Bs))
    (M : GGQ2LDatum 3 Bs L x) {N : ℕ} (h2 : 2 ≤ N)
    (f : Fin N → M.V) (hf : GGQ2S08ROFrame M f) (Q : Fin N → Subgroup G)
    (hQle : ∀ j, Q j ≤ L)
    (hQcomp : ∀ j, LargeEvenPComponent 3 (Subgroup.centralizer
      ({x, ((ggQ2s08r4_b M f j : ↥Bs) : G)} : Set G)) (Q j))
    (hQnorm : ∀ j, Bs ≤ Subgroup.normalizer (Q j : Set G))
    (hQa : ∀ j, 4 ∣ Nat.card ↥(ggAutomizer (Q j) Bs))
    (hQgen : ∀ i j, i ≠ j → Q i ⊔ Q j = L)
    (hD : ∀ T : M.V ≃ₗ[ZMod 3] M.V, GGQ2S08MonoEven f T →
      ∃ (m : G) (θ : MulAut ↥Bs), GGQ2Ind Bs m θ ∧
        m ∈ Subgroup.normalizer (ggG0 3 B x L D J : Set G) ∧
        ggLin (p := 3) M.model θ = T)
    {g : G} {φ : MulAut ↥Bs} (hInd : GGQ2Ind Bs g φ)
    {k : Fin N} (hlin : ggLin (p := 3) M.model φ =
      ggQ2s08r4_singleEquiv M (ggQ2s08r4_basis M f hf) k) :
    L.map (MulAut.conj g).toMonoidHom ≤ ggG0 3 B x L D J := by
  have hLpair : GGStdPair' 3 Bs x L := ggStdPair'_L hP hS.1 hCav
  have hx : g * x * g⁻¹ = x * ((ggQ2s08r4_b M f k : ↥Bs) : G) := by
    have h := ggQ2s08r4_conj_eq_of_lin M hInd ⟨x, M.hx⟩
      (⟨x, M.hx⟩ * ggQ2s08r4_b M f k) (by
        rw [hlin]; exact ggQ2s08r4_single_lin_model_x M f hf k)
    simpa [Subgroup.coe_mul] using h
  have hb : g * ((ggQ2s08r4_b M f k : ↥Bs) : G) * g⁻¹ =
      ((ggQ2s08r4_b M f k)⁻¹ : ↥Bs) := by
    have h := ggQ2s08r4_conj_eq_of_lin M hInd (ggQ2s08r4_b M f k) (ggQ2s08r4_b M f k)⁻¹ (by
      rw [hlin]; exact ggQ2s08r4_single_lin_model_b_self M f hf k)
    simpa using h
  have hQk_le : (Q k).map (MulAut.conj g).toMonoidHom ≤ L := by
    have hcent := ggQ2s08r4_centralizer_conj_eq'
      (x := x) (a := ((ggQ2s08r4_b M f k : ↥Bs) : G))
      (u := x * ((ggQ2s08r4_b M f k : ↥Bs) : G))
      (w := ((ggQ2s08r4_b M f k : ↥Bs) : G)⁻¹) hx hb
    have hcomp : LargeEvenPComponent 3
        (Subgroup.centralizer (Subgroup.closure
          ({x, ((ggQ2s08r4_b M f k : ↥Bs) : G)} : Set G) : Set G))
        ((Q k).map (MulAut.conj g).toMonoidHom) := by
      have h := largeEvenPComponent_map_conj' (g := g) (hQcomp k)
      rw [hcent, ← ggQ2s08r4_closure_pair_mul_inv x ((ggQ2s08r4_b M f k : ↥Bs) : G)] at h
      exact h
    have hQa' : 4 ∣ Nat.card ↥(ggAutomizer ((Q k).map (MulAut.conj g).toMonoidHom) Bs) :=
      (hQa k).trans (ggQ2s08r4_automizer_map_conj_dvd hInd.1)
    have hFBs : Subgroup.closure ({x, ((ggQ2s08r4_b M f k : ↥Bs) : G)} : Set G) ≤ Bs := by
      rw [Subgroup.closure_le]
      rintro z (rfl | rfl)
      · exact M.hx
      · exact (ggQ2s08r4_b M f k).2
    have hwF : x ∈ Subgroup.closure ({x, ((ggQ2s08r4_b M f k : ↥Bs) : G)} : Set G) :=
      Subgroup.subset_closure (Or.inl rfl)
    exact ggQ2n_absorb hLB hS.1 rfl hFBs hwF hLpair hcomp hQa'
  have hQj_le : ∀ j : Fin N, j ≠ k →
      (Q j).map (MulAut.conj g).toMonoidHom ≤ ggG0 3 B x L D J := by
    intro j hjk
    have hTeven : GGQ2S08MonoEven f
        (ggQ2s08r4_singleEquiv M (ggQ2s08r4_basis M f hf) k *
          ggQ2s08r4_singleEquiv M (ggQ2s08r4_basis M f hf) j) :=
      ggQ2s08r4_monoEven_mul_single M f hf j k
    obtain ⟨m, θ, hIndm, hmG0, hmlin⟩ := hD _ hTeven
    have hmx : m * x * m⁻¹ =
        x * ((ggQ2s08r4_b M f k : ↥Bs) : G) * ((ggQ2s08r4_b M f j : ↥Bs) : G) := by
      have h := ggQ2s08r4_conj_eq_of_lin M hIndm ⟨x, M.hx⟩
        (⟨x, M.hx⟩ * ggQ2s08r4_b M f k * ggQ2s08r4_b M f j) (by
          rw [hmlin]; exact ggQ2s08r4_mul_single_lin_model_x M f hf hjk)
      simpa [Subgroup.coe_mul] using h
    have hbj : g * ((ggQ2s08r4_b M f j : ↥Bs) : G) * g⁻¹ =
        ((ggQ2s08r4_b M f j : ↥Bs) : G) := by
      have h := ggQ2s08r4_conj_eq_of_lin M hInd (ggQ2s08r4_b M f j) (ggQ2s08r4_b M f j) (by
        rw [hlin]; exact ggQ2s08r4_single_lin_model_b_ne M f hf hjk)
      simpa using h
    have hcentj := ggQ2s08r4_centralizer_conj_eq'
      (x := x) (a := ((ggQ2s08r4_b M f j : ↥Bs) : G))
      (u := x * ((ggQ2s08r4_b M f k : ↥Bs) : G))
      (w := ((ggQ2s08r4_b M f j : ↥Bs) : G)) hx hbj
    have hcompj : LargeEvenPComponent 3
        (Subgroup.centralizer (Subgroup.closure
          ({x * ((ggQ2s08r4_b M f k : ↥Bs) : G),
            ((ggQ2s08r4_b M f j : ↥Bs) : G)} : Set G) : Set G))
        ((Q j).map (MulAut.conj g).toMonoidHom) := by
      have h := largeEvenPComponent_map_conj' (g := g) (hQcomp j)
      rw [hcentj] at h
      exact h
    have hQaj' : 4 ∣ Nat.card ↥(ggAutomizer ((Q j).map (MulAut.conj g).toMonoidHom) Bs) :=
      (hQa j).trans (ggQ2s08r4_automizer_map_conj_dvd hInd.1)
    have hLm_pair : GGStdPair' 3 Bs (m * x * m⁻¹)
        (L.map (MulAut.conj m).toMonoidHom) :=
      ggStdPair'_conj hIndm.1 hLpair
    rw [hmx] at hLm_pair
    have hF'Bs : Subgroup.closure
        ({x * ((ggQ2s08r4_b M f k : ↥Bs) : G),
          ((ggQ2s08r4_b M f j : ↥Bs) : G)} : Set G) ≤ Bs := by
      rw [Subgroup.closure_le]
      rintro z (rfl | rfl)
      · exact Bs.mul_mem M.hx (ggQ2s08r4_b M f k).2
      · exact (ggQ2s08r4_b M f j).2
    have hwF' : x * ((ggQ2s08r4_b M f k : ↥Bs) : G) * ((ggQ2s08r4_b M f j : ↥Bs) : G) ∈
        Subgroup.closure
          ({x * ((ggQ2s08r4_b M f k : ↥Bs) : G),
            ((ggQ2s08r4_b M f j : ↥Bs) : G)} : Set G) :=
      Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inl rfl))
        (Subgroup.subset_closure (Or.inr rfl))
    have habs := ggQ2n_absorb hLB hS.1 rfl hF'Bs hwF' hLm_pair hcompj hQaj'
    have hLm_le : L.map (MulAut.conj m).toMonoidHom ≤ ggG0 3 B x L D J :=
      calc L.map (MulAut.conj m).toMonoidHom
          ≤ (ggG0 3 B x L D J).map (MulAut.conj m).toMonoidHom :=
            Subgroup.map_mono (le_ggG0_left 3 B x L D J)
        _ = ggG0 3 B x L D J := map_conj_eq_of_mem_normalizer hmG0
    exact habs.trans hLm_le
  haveI : Nontrivial (Fin N) :=
    ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp⟩
  obtain ⟨j, hjk⟩ := exists_ne k
  have hgen : Q k ⊔ Q j = L := hQgen k j (Ne.symm hjk)
  conv_lhs => rw [← hgen]
  rw [Subgroup.map_sup]
  exact sup_le (hQk_le.trans (le_ggG0_left 3 B x L D J)) (hQj_le j hjk)

end CFSG.StandardType

end
