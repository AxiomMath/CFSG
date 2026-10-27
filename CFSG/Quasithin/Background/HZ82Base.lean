module

public import CFSG.Quasithin.Background.HTransport

public section

namespace CFSG.Quasithin.H.ZTrans

open CFSG.Open

variable {V W : Type*} [CommGroup V] [CommGroup W]

theorem inf_centSub_map_congrHom (e : V ≃* W) (H : Subgroup (MulAut V)) (z : V) :
    (H ⊓ centSub (Subgroup.zpowers z)).map (congrHom e) =
      H.map (congrHom e) ⊓ centSub (Subgroup.zpowers (e z)) := by
  rw [Subgroup.map_inf _ _ _ (congrHom_injective e), centSub_map_congrHom, MonoidHom.map_zpowers]
  rfl

omit [CommGroup W] in
theorem finite_mulAut_z [Finite V] : Finite (MulAut V) :=
  Finite.of_injective (fun f : MulAut V => (f : V → V)) DFunLike.coe_injective

theorem perfectCore_map_congrHom [Finite V] [Finite W] (e : V ≃* W) (X : Subgroup (MulAut V)) :
    perfectCore (X.map (congrHom e)) = (perfectCore X).map (congrHom e) := by
  have : Finite (MulAut V) := finite_mulAut_z (V := V)
  have : Finite (MulAut W) := finite_mulAut_z (V := W)
  exact (map_perfectCore _ _).symm

theorem pCoreOf_map_congrHom (e : V ≃* W) (X : Subgroup (MulAut V)) :
    pCoreOf 2 (X.map (congrHom e)) = (pCoreOf 2 X).map (congrHom e) :=
  CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 (MulAut.congr e) X

theorem commV_map_congrHom (e : V ≃* W) (X : Subgroup (MulAut V)) :
    commV (X.map (congrHom e)) = (commV X).map e.toMonoidHom :=
  commV_map_congr_equiv e X

theorem stabSub_map_congrHom (e : V ≃* W) (U : Subgroup V) :
    stabSub (U.map e.toMonoidHom) = (stabSub U).map (congrHom e) :=
  CFSG.Quasithin.StabLat.stabSub_map_equiv e U

theorem pCoreOf_map_of_injective {G G' : Type*} [Group G] [Group G'] (p : ℕ) (f : G →* G')
    (hf : Function.Injective f) (X : Subgroup G) :
    pCoreOf p (X.map f) = (pCoreOf p X).map f := by
  let e : G ≃* f.range := MonoidHom.ofInjective hf
  have h1 : X.map f = (X.map e.toMonoidHom).map f.range.subtype := by
    rw [Subgroup.map_map]
    rfl
  have h2 : ∀ Y : Subgroup f.range, pCoreOf p (Y.map f.range.subtype) =
      (pCoreOf p Y).map f.range.subtype := by
    intro Y
    unfold pCoreOf
    let φ : Y ≃* Y.map f.range.subtype := Y.equivMapOfInjective _ f.range.subtype_injective
    rw [← CFSG.LieType.BorelTits.map_pCore_mulEquiv p φ, Subgroup.map_map, Subgroup.map_map]
    rfl
  rw [h1, h2, CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv p e X, Subgroup.map_map]
  rfl

theorem commV_closure_le (s : Set (MulAut V)) (U : Subgroup V)
    (h : ∀ g ∈ s, ∀ v, g v * v⁻¹ ∈ U) : commV (Subgroup.closure s) ≤ U := by
  have key : ∀ x ∈ Subgroup.closure s, ∀ v, x v * v⁻¹ ∈ U := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact h x hx
    | one => intro v; simp
    | mul x y _ _ ihx ihy =>
      intro v
      have e : (x * y) v * v⁻¹ = (x (y v) * (y v)⁻¹) * (y v * v⁻¹) := by
        rw [MulAut.mul_apply]
        group
      rw [e]
      exact U.mul_mem (ihx (y v)) (ihy v)
    | inv x _ ih =>
      intro v
      have e : x⁻¹ v * v⁻¹ = (x (x⁻¹ v) * (x⁻¹ v)⁻¹)⁻¹ := by
        rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
        group
      rw [e]
      exact U.inv_mem (ih _)
  rw [commV, Subgroup.closure_le]
  rintro _ ⟨x, hx, v, rfl⟩
  exact key x hx v

theorem mem_commV {X : Subgroup (MulAut V)} {g : MulAut V} (hg : g ∈ X) (v : V) :
    g v * v⁻¹ ∈ commV X :=
  Subgroup.subset_closure ⟨g, hg, v, rfl⟩

@[expose] def moveSub (U : Subgroup V) : Subgroup (MulAut V) where
  carrier := {g | ∀ v, g v * v⁻¹ ∈ U}
  mul_mem' := by
    intro g h hg hh v
    have e : (g * h) v * v⁻¹ = (g (h v) * (h v)⁻¹) * (h v * v⁻¹) := by
      rw [MulAut.mul_apply]
      group
    rw [e]
    exact U.mul_mem (hg _) (hh v)
  one_mem' := fun v => by simp
  inv_mem' := by
    intro g hg v
    have e : g⁻¹ v * v⁻¹ = (g (g⁻¹ v) * (g⁻¹ v)⁻¹)⁻¹ := by
      rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
      group
    rw [e]
    exact U.inv_mem (hg _)

theorem commV_le_iff {X : Subgroup (MulAut V)} {U : Subgroup V} : commV X ≤ U ↔ X ≤ moveSub U := by
  constructor
  · intro h g hg v
    exact h (mem_commV hg v)
  · intro h
    rw [commV, Subgroup.closure_le]
    rintro _ ⟨x, hx, v, rfl⟩
    exact h hx v

theorem exists_conj_eq_of_fixV [Finite V] {H S K : Subgroup (MulAut V)} (hSH : S ≤ H)
    (hS : Nat.card ↥S = 2 ^ (Nat.card ↥H).factorization 2) (hKH : K ≤ H) (hK : IsPGroup 2 ↥K)
    {w₀ : V} (hfix : ∀ w ∈ fixV K, w = 1 ∨ w = w₀) {z : V} (hz : z ∈ fixV S) (hz1 : z ≠ 1) :
    ∃ h ∈ H, h z = w₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut V) :=
    Finite.of_injective (fun f : MulAut V => (f : V → V)) DFunLike.coe_injective
  let T : Sylow 2 ↥H := Sylow.ofCard (S.subgroupOf H) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSH).toEquiv]
    exact hS)
  have hK' : IsPGroup 2 ↥(K.subgroupOf H) :=
    hK.of_equiv (Subgroup.subgroupOfEquivOfLe hKH).symm
  obtain ⟨Q, hQ⟩ := hK'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥H T Q
  have key : ∀ x ∈ K, (g : MulAut V)⁻¹ * x * g ∈ S := by
    intro x hx
    have h1 : (⟨x, hKH hx⟩ : ↥H) ∈ (Q : Subgroup ↥H) := hQ (Subgroup.mem_subgroupOf.2 hx)
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h1
    have h2 := Subgroup.mem_subgroupOf.1 h1
    simpa [MulAut.smul_def, MulAut.conj_inv_apply] using h2
  have hgz : (g : MulAut V) z ∈ fixV K := by
    intro x hx
    have h3 : (g : MulAut V)⁻¹ (x ((g : MulAut V) z)) = z := hz _ (key x hx)
    calc x ((g : MulAut V) z)
        = (g : MulAut V) ((g : MulAut V)⁻¹ (x ((g : MulAut V) z))) :=
          (MulEquiv.apply_symm_apply _ _).symm
      _ = (g : MulAut V) z := by rw [h3]
  rcases hfix _ hgz with h1 | h1
  · exact absurd ((g : MulAut V).injective (h1.trans (map_one _).symm)) hz1
  · exact ⟨g, g.2, h1⟩

@[expose] def parZ (H : Subgroup (MulAut V)) (z : V) : Subgroup (MulAut V) :=
  perfectCore (H ⊓ centSub (Subgroup.zpowers z))

@[expose] def radZ (H : Subgroup (MulAut V)) (z : V) : Subgroup (MulAut V) :=
  pCoreOf 2 (parZ H z)

@[expose] def vZ (H : Subgroup (MulAut V)) (z : V) : Subgroup V := commV (radZ H z)

theorem parZ_map [Finite V] [Finite W] (e : V ≃* W) (H : Subgroup (MulAut V)) (z : V) :
    (parZ H z).map (congrHom e) = parZ (H.map (congrHom e)) (e z) := by
  rw [parZ, parZ, ← perfectCore_map_congrHom, inf_centSub_map_congrHom]

theorem radZ_map [Finite V] [Finite W] (e : V ≃* W) (H : Subgroup (MulAut V)) (z : V) :
    (radZ H z).map (congrHom e) = radZ (H.map (congrHom e)) (e z) := by
  rw [radZ, radZ, ← parZ_map, pCoreOf_map_congrHom]

theorem vZ_map [Finite V] [Finite W] (e : V ≃* W) (H : Subgroup (MulAut V)) (z : V) :
    (vZ H z).map e.toMonoidHom = vZ (H.map (congrHom e)) (e z) := by
  rw [vZ, vZ, ← radZ_map, commV_map_congrHom]

@[expose] def HZConcl (H : Subgroup (MulAut V)) (z : V) (k : ℕ) : Prop :=
  Nat.card ↥(vZ H z) = 2 ^ (k + 1) ∧ Nat.card ↥(radZ H z) = 2 ^ k ∧
    ⁅radZ H z, parZ H z⁆ = radZ H z ∧
    (∀ N : Subgroup (MulAut V), N ≤ radZ H z → N ≠ ⊥ →
      parZ H z ≤ Subgroup.normalizer (N : Set (MulAut V)) → N = radZ H z) ∧
    (∀ Y : Subgroup V, Subgroup.zpowers z < Y → Y ≤ vZ H z → parZ H z ≤ stabSub Y →
      Y = vZ H z) ∧
    vZ H z ⊓ fixV (radZ H z) = Subgroup.zpowers z ∧ commV (parZ H z) = ⊤

theorem HZConcl.of_map [Finite V] [Finite W] (e : V ≃* W) {H : Subgroup (MulAut V)} {z : V}
    {k : ℕ} (h : HZConcl (H.map (congrHom e)) (e z) k) : HZConcl H z k := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  have hinj := congrHom_injective e
  have hP := parZ_map e H z
  have hR := radZ_map e H z
  have hW := vZ_map e H z
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← h1, ← hW, Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]
  · rw [← h2, ← hR, card_map_congrHom]
  · apply Subgroup.map_injective hinj
    rw [Subgroup.map_commutator, hR, hP, h3]
  · intro N hN hN1 hPN
    apply Subgroup.map_injective hinj
    rw [hR]
    refine h4 _ (hR ▸ Subgroup.map_mono hN) ?_ ?_
    · rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ hinj]
    · rw [← hP, ← Subgroup.map_equiv_normalizer_eq N (MulAut.congr e)]
      exact Subgroup.map_mono hPN
  · intro Y hY1 hY2 hY3
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [hW]
    refine h5 _ ?_ (hW ▸ Subgroup.map_mono hY2) ?_
    · have hz : Subgroup.zpowers (e z) = (Subgroup.zpowers z).map e.toMonoidHom :=
        (MonoidHom.map_zpowers e.toMonoidHom z).symm
      rw [hz]
      exact (Subgroup.map_lt_map_iff_of_injective (f := e.toMonoidHom) e.injective).2 hY1
    · rw [← hP, stabSub_map_congrHom]
      exact Subgroup.map_mono hY3
  · apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    have hz : (Subgroup.zpowers z).map e.toMonoidHom = Subgroup.zpowers (e z) :=
      MonoidHom.map_zpowers e.toMonoidHom z
    rw [Subgroup.map_inf _ _ _ e.injective, hW, ← fixV_map_congrHom, hR, hz]
    exact h6
  · apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [Subgroup.map_top_of_surjective _ e.surjective, ← commV_map_congrHom, hP]
    exact h7

theorem map_congrHom_self {H₀ : Subgroup (MulAut W)} {h : MulAut W} (hh : h ∈ H₀) :
    H₀.map (congrHom h) = H₀ := by
  have key : ∀ y, congrHom h y = h * y * h⁻¹ := fun y => by
    ext w
    rfl
  refine le_antisymm ?_ ?_
  · rintro _ ⟨y, hy, rfl⟩
    rw [key]
    exact H₀.mul_mem (H₀.mul_mem hh hy) (H₀.inv_mem hh)
  · intro y hy
    refine ⟨h⁻¹ * y * h, H₀.mul_mem (H₀.mul_mem (H₀.inv_mem hh) hy) hh, ?_⟩
    rw [key]
    group

theorem exists_equiv_std (e₀ : V ≃* W) {H : Subgroup (MulAut V)} {H₀ : Subgroup (MulAut W)}
    (hH : H.map (congrHom e₀) = H₀) {z : V} {z₀ : W} {h : MulAut W} (hh : h ∈ H₀)
    (hz : h (e₀ z) = z₀) : ∃ e : V ≃* W, H.map (congrHom e) = H₀ ∧ e z = z₀ := by
  refine ⟨e₀.trans h, ?_, hz⟩
  have hc : congrHom (e₀.trans h) = (congrHom h).comp (congrHom e₀) := by
    ext x w
    rfl
  rw [hc, ← Subgroup.map_map, hH, map_congrHom_self hh]

end CFSG.Quasithin.H.ZTrans
