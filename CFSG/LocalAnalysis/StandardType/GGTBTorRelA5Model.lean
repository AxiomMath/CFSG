module

public import CFSG.LocalAnalysis.StandardType.GGTBTorRelA5Coord
public import CFSG.LocalAnalysis.StandardType.GGTBTorRelA5Lift
public import CFSG.LocalAnalysis.StandardType.GGTBTorRelA5Marked

@[expose] public section

namespace CFSG.StandardType.RelA5

open CFSG CFSG.Assembly Multiplicative

section PCoord

variable {μ : Type} [CommGroup μ] {p : ℕ} [NeZero p]

def embPow (ζ : μ) (hζ : ζ ^ p = 1) :
    (Fin 3 → Multiplicative (ZMod p)) →* (Fin 3 → μ) where
  toFun f i := ζ ^ (toAdd (f i)).val
  map_one' := by
    funext i
    simp
  map_mul' f g := by
    funext i
    have hmod : ∀ x : ℕ, ζ ^ (x % p) = ζ ^ x := fun x => by
      conv_rhs => rw [← Nat.mod_add_div x p, pow_add, pow_mul, hζ, one_pow, mul_one]
    simp only [Pi.mul_apply, toAdd_mul]
    rw [ZMod.val_add, hmod, pow_add]

theorem embPow_apply (ζ : μ) (hζ : ζ ^ p = 1) (f : Fin 3 → Multiplicative (ZMod p)) (i : Fin 3) :
    embPow ζ hζ f i = ζ ^ (toAdd (f i)).val :=
  rfl

theorem pow_val_neg {ζ : μ} (hζ : ζ ^ p = 1) (a : ZMod p) : ζ ^ (-a).val = (ζ ^ a.val)⁻¹ := by
  have hmod : ∀ x : ℕ, ζ ^ (x % p) = ζ ^ x := fun x => by
    conv_rhs => rw [← Nat.mod_add_div x p, pow_add, pow_mul, hζ, one_pow, mul_one]
  have h0 : (-a + a).val = 0 := by rw [neg_add_cancel, ZMod.val_zero]
  rw [eq_inv_iff_mul_eq_one, ← pow_add, ← hmod, ← ZMod.val_add, h0, pow_zero]

theorem embPow_injective {ζ : μ} (hζ : IsPrimitiveRoot ζ p) :
    Function.Injective (embPow ζ hζ.pow_eq_one) := by
  intro f g h
  funext i
  have h1 := congrFun h i
  simp only [embPow_apply] at h1
  exact toAdd.injective (ZMod.val_injective p (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h1))

theorem embPow_pow (ζ : μ) (hζ : ζ ^ p = 1) (f : Fin 3 → Multiplicative (ZMod p)) :
    embPow ζ hζ f ^ p = 1 := by
  funext i
  rw [Pi.pow_apply, embPow_apply, ← pow_mul, mul_comm, pow_mul, hζ, one_pow, Pi.one_apply]

theorem embPow_spReflAut (ζ : μ) (hζ : ζ ^ p = 1) (k : Fin 3)
    (f : Fin 3 → Multiplicative (ZMod p)) :
    embPow ζ hζ (ggSpSigned_spReflAut p 3 k f) = refl k (embPow ζ hζ f) := by
  funext i
  fin_cases k <;> fin_cases i <;>
    simp [ggSpSigned_spReflAut, SpCoord.permAut_apply, SpCoord.sgnAut_apply, refl, embPow_apply,
      Equiv.swap_apply_def]
  exact pow_val_neg hζ _

end PCoord

theorem eq_one_of_mem_center_of_pow {H : Type} [Group H] [Finite H] {p : ℕ} (hp : p.Prime)
    (hZp : ¬ p ∣ Nat.card (Subgroup.center H)) {c : H} (hc : c ∈ Subgroup.center H)
    (hcp : c ^ p = 1) : c = 1 := by
  have h1 : orderOf c ∣ p := orderOf_dvd_of_pow_eq_one hcp
  have h2 : orderOf c ∣ Nat.card (Subgroup.center H) := by
    have := Subgroup.orderOf_dvd_natCard (Subgroup.center H) hc
    exact this
  rcases (Nat.dvd_prime hp).mp h1 with h | h
  · exact orderOf_eq_one_iff.mp h
  · exact absurd (h ▸ h2) hZp

theorem mul_inv_mem_center_of_conj_eq {G : Type} [Group G] {u v : G}
    (h : MulAut.conj u = MulAut.conj v) : u * v⁻¹ ∈ Subgroup.center G := by
  rw [Subgroup.mem_center_iff]
  intro y
  have h1 := congrArg (fun ψ : MulAut G => ψ (v⁻¹ * y * v)) h
  simp only [MulAut.conj_apply] at h1
  calc y * (u * v⁻¹) = (u * (v⁻¹ * y * v) * u⁻¹) * (u * v⁻¹) := by rw [h1]; group
    _ = u * v⁻¹ * y := by group

theorem pow_prime_eq_one {p : ℕ} (f : Fin 3 → Multiplicative (ZMod p)) : f ^ p = 1 := by
  funext i
  rw [Pi.pow_apply, Pi.one_apply]
  apply toAdd.injective
  rw [toAdd_pow, toAdd_one, nsmul_eq_mul, ZMod.natCast_self, zero_mul]

theorem ggTorusTorData_of_relA5Model {p m : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hm : Odd m)
    {L' H : Type} [Group L'] [Group H] [Finite H]
    (Φ : H →* L') (hΦ : Function.Surjective Φ) (hΦker : Φ.ker ≤ Subgroup.center H)
    (hHperf : commutator H = ⊤) (hZp : ¬ p ∣ Nat.card (Subgroup.center H))
    (hZm : Nat.Coprime m (Nat.card (Subgroup.center H)))
    {μ : Type} [CommGroup μ] (l : μ ≃* Multiplicative (ZMod m)) (hμ : ∀ x : μ, x ^ m = 1)
    (F : (Fin 3 → μ) →* H) (hFZ : ∀ z, F z ∈ Subgroup.center H → z = 1)
    (TH : Subgroup H) (hTH : ∀ x ∈ TH, ∀ y ∈ TH, Commute x y) (hFT : ∀ z, F z ∈ TH)
    (hTHm : ∀ t ∈ TH, t ^ m = 1 → ∃ z, F z = t) (hZT : Subgroup.center H ≤ TH)
    (hcentH : ∀ g : H, (∀ z : Fin 3 → μ, (∀ i, z i ^ p = 1) → Commute g (F z)) → g ∈ TH)
    (w : Fin 3 → H) (hw : ∀ k z, w k * F z * (w k)⁻¹ = F (refl k z))
    (ζ : μ) (hζ : IsPrimitiveRoot ζ p)
    (hpt : ∀ z : Fin 3 → μ, (∀ i, z i ^ p = 1) → z ∈ (embPow ζ hζ.pow_eq_one).range)
    (hSN : ∀ g : H, (∀ f, ∃ f', g * F (embPow ζ hζ.pow_eq_one f) * g⁻¹ =
        F (embPow ζ hζ.pow_eq_one f')) →
      ∃ (π : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod p), (∀ i, ε i = 1 ∨ ε i = -1) ∧
        ∀ f f', g * F (embPow ζ hζ.pow_eq_one f) * g⁻¹ = F (embPow ζ hζ.pow_eq_one f') →
          ∀ i, toAdd (f' (π i)) = ε i * toAdd (f i))
    {A : Subgroup (MulAut L')}
    (hA : A = (((embPow ζ hζ.pow_eq_one).range.map F).map Φ).map
      (MulAut.conj : L' →* MulAut L')) :
    GGTorusTorData m 3 (CartanMatrix.C 3) (CoxeterMatrix.B 3) L' A := by
  classical
  have hp : p.Prime := Fact.out
  set ep := embPow ζ hζ.pow_eq_one with hep
  let ι : (Fin 3 → Multiplicative (ZMod p)) →* H := F.comp ep
  have hcen : ∀ x : H, Φ x ∈ Subgroup.center L' → x ∈ Subgroup.center H := fun x hx =>
    mem_center_of_map_mem_center hHperf hΦker hx
  have hFker : ∀ z, Φ (F z) = 1 → z = 1 := fun z hz => hFZ z (hΦker hz)
  let φ : (Fin 3 → μ) →* L' := Φ.comp (F.comp (rootInv m))
  have hφ_apply : ∀ b, φ b = Φ (F (rootInv m b)) := fun _ => rfl
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro b hb
    exact rootInv_injective hm hμ ((hFker _ hb).trans (map_one _).symm)
  have hφZ : ∀ b, φ b ∈ Subgroup.center L' → b = 1 := fun b hb =>
    rootInv_injective hm hμ ((hFZ _ (hcen _ hb)).trans (map_one _).symm)
  let Tsc : Subgroup L' := TH.map Φ
  have hTsc_comm : ∀ b, ∀ t ∈ Tsc, Commute (φ b) t := by
    rintro b _ ⟨t, ht, rfl⟩
    exact (hTH _ (hFT _) t ht).map Φ
  have hTsc_tors : ∀ t ∈ Tsc, t ^ m = 1 → t ∈ φ.range := by
    rintro _ ⟨t, ht, rfl⟩ htm
    have hz : t ^ m ∈ Φ.ker := by rw [MonoidHom.mem_ker, map_pow, htm]
    have hcop : (Nat.card Φ.ker).Coprime m := by
      refine Nat.Coprime.coprime_dvd_left ?_ hZm.symm
      exact Subgroup.card_dvd_of_le hΦker
    obtain ⟨w₀, hw₀⟩ := (Nat.Coprime.pow_left_bijective hcop).2 ⟨t ^ m, hz⟩
    have hw₀' : ((w₀ : H)) ^ m = t ^ m := by
      have := congrArg Subtype.val hw₀
      simpa using this
    have hw₀Z : (w₀ : H) ∈ Subgroup.center H := hΦker w₀.2
    have hcomm : Commute t (w₀ : H) := Subgroup.mem_center_iff.mp hw₀Z t
    have ht' : t * (w₀ : H)⁻¹ ∈ TH := TH.mul_mem ht (TH.inv_mem (hZT hw₀Z))
    have ht'm : (t * (w₀ : H)⁻¹) ^ m = 1 := by
      rw [hcomm.inv_right.mul_pow, inv_pow, hw₀', mul_inv_cancel]
    obtain ⟨z, hz'⟩ := hTHm _ ht' ht'm
    refine ⟨root z, ?_⟩
    rw [hφ_apply, rootInv_root hm hμ, hz', map_mul, map_inv,
      show Φ (w₀ : H) = 1 from w₀.2, inv_one, mul_one]
  have hTsc_odd : ∀ z ∈ Subgroup.center L', Odd (orderOf z) → z ∈ Tsc := by
    intro z hz _
    obtain ⟨x, rfl⟩ := hΦ z
    exact ⟨x, hZT (hcen x hz), rfl⟩
  let E : Subgroup L' := ((ep.range).map F).map Φ
  have hmemE : ∀ g, g ∈ E ↔ ∃ f, Φ (ι f) = g := by
    intro g
    constructor
    · rintro ⟨_, ⟨_, ⟨f, rfl⟩, rfl⟩, rfl⟩
      exact ⟨f, rfl⟩
    · rintro ⟨f, rfl⟩
      exact ⟨ι f, ⟨ep f, ⟨f, rfl⟩, rfl⟩, rfl⟩
  have hE : ∀ g, g ∈ E ↔ g ^ p = 1 ∧ g ∈ φ.range := by
    intro g
    rw [hmemE]
    constructor
    · rintro ⟨f, rfl⟩
      refine ⟨?_, ⟨root (ep f), ?_⟩⟩
      · rw [← map_pow, ← map_pow, pow_prime_eq_one, map_one, map_one]
      · rw [hφ_apply, rootInv_root hm hμ]
        rfl
    · rintro ⟨hgp, b, rfl⟩
      have hbp : b ^ p = 1 := hφinj (by rw [map_pow, hgp, map_one])
      have hzp : ∀ i, rootInv m b i ^ p = 1 := by
        intro i
        rw [← Pi.pow_apply, ← map_pow, hbp, map_one, Pi.one_apply]
      obtain ⟨f, hf⟩ := hpt _ hzp
      exact ⟨f, by rw [hφ_apply, ← hf]; rfl⟩
  have hcp : ∀ c : H, c ∈ Subgroup.center H → c ^ p = 1 → c = 1 := fun c hc hcp =>
    eq_one_of_mem_center_of_pow hp hZp hc hcp
  have hιp : ∀ f, ι f ^ p = 1 := fun f => by rw [← map_pow, pow_prime_eq_one, map_one]
  have hlift : ∀ (x : H) (f f' : Fin 3 → Multiplicative (ZMod p)),
      MulAut.conj (Φ (x * ι f * x⁻¹)) = MulAut.conj (Φ (ι f')) → x * ι f * x⁻¹ = ι f' := by
    intro x f f' h
    have hcZ : x * ι f * x⁻¹ * (ι f')⁻¹ ∈ Subgroup.center H := by
      refine hcen _ ?_
      rw [map_mul, map_inv]
      exact mul_inv_mem_center_of_conj_eq h
    have hcomm : Commute (x * ι f * x⁻¹ * (ι f')⁻¹) (ι f') :=
      (Subgroup.mem_center_iff.mp hcZ (ι f')).symm
    have hc1 : (x * ι f * x⁻¹ * (ι f')⁻¹) ^ p = 1 := by
      have h2 : (x * ι f * x⁻¹ * (ι f')⁻¹) ^ p * ι f' ^ p = (x * ι f * x⁻¹) ^ p := by
        rw [← hcomm.mul_pow, inv_mul_cancel_right]
      rw [hιp, mul_one, conj_pow, hιp, mul_one, mul_inv_cancel] at h2
      exact h2
    have := hcp _ hcZ hc1
    rwa [mul_inv_eq_one] at this
  have hcent : ∀ g : L', (∀ e ∈ E, g * e * g⁻¹ * e⁻¹ ∈ Subgroup.center L') →
      g ∈ Tsc ⊔ Subgroup.center L' := by
    intro g hg
    obtain ⟨x, rfl⟩ := hΦ g
    have hxι : ∀ f, Commute x (ι f) := by
      intro f
      have h1 := hg (Φ (ι f)) ((hmemE _).mpr ⟨f, rfl⟩)
      have hcZ : x * ι f * x⁻¹ * (ι f)⁻¹ ∈ Subgroup.center H := by
        refine hcen _ ?_
        simpa only [map_mul, map_inv] using h1
      have hcomm : Commute (x * ι f * x⁻¹ * (ι f)⁻¹) (ι f) :=
        (Subgroup.mem_center_iff.mp hcZ (ι f)).symm
      have hc1 : (x * ι f * x⁻¹ * (ι f)⁻¹) ^ p = 1 := by
        have h2 : (x * ι f * x⁻¹ * (ι f)⁻¹) ^ p * ι f ^ p = (x * ι f * x⁻¹) ^ p := by
          rw [← hcomm.mul_pow, inv_mul_cancel_right]
        rw [hιp, mul_one, conj_pow, hιp, mul_one, mul_inv_cancel] at h2
        exact h2
      have h3 := hcp _ hcZ hc1
      rw [mul_inv_eq_one] at h3
      change x * ι f = ι f * x
      calc x * ι f = x * ι f * x⁻¹ * x := by group
        _ = ι f * x := by rw [h3]
    have hxT : x ∈ TH := hcentH x fun z hz => by
      obtain ⟨f, rfl⟩ := hpt z hz
      exact hxι f
    exact Subgroup.mem_sup_left ⟨x, hxT, rfl⟩
  let n : Fin 3 → L' := fun k => Φ (w k)
  have hwι : ∀ k f, w k * ι f * (w k)⁻¹ = ι (ggSpSigned_spReflAut p 3 k f) := by
    intro k f
    change w k * F (ep f) * (w k)⁻¹ = F (ep (ggSpSigned_spReflAut p 3 k f))
    rw [hw, hep, embPow_spReflAut]
  have hwι' : ∀ k f, (w k)⁻¹ * ι f * w k = ι ((ggSpSigned_spReflAut p 3 k)⁻¹ f) := by
    intro k f
    have h1 := hwι k ((ggSpSigned_spReflAut p 3 k)⁻¹ f)
    have h2 : (ggSpSigned_spReflAut p 3 k) ((ggSpSigned_spReflAut p 3 k)⁻¹ f) = f :=
      MulEquiv.apply_symm_apply _ f
    rw [h2] at h1
    calc (w k)⁻¹ * ι f * w k
        = (w k)⁻¹ * (w k * ι ((ggSpSigned_spReflAut p 3 k)⁻¹ f) * (w k)⁻¹) * w k := by rw [h1]
      _ = ι ((ggSpSigned_spReflAut p 3 k)⁻¹ f) := by
          simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
  have hconjA : ∀ (k : Fin 3) (a : MulAut L'), a ∈ scalarA E →
      MulAut.conj (n k) * a * (MulAut.conj (n k))⁻¹ ∈ scalarA E := by
    rintro k a ⟨e, he, rfl⟩
    obtain ⟨f, rfl⟩ := (hmemE e).mp he
    refine ⟨Φ (ι (ggSpSigned_spReflAut p 3 k f)), (hmemE _).mpr ⟨_, rfl⟩, ?_⟩
    rw [← hwι, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv]
  have hn : ∀ k, MulAut.conj (n k) ∈ Subgroup.normalizer ((scalarA E) : Set (MulAut L')) := by
    intro k
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · exact hconjA k a
    · rintro ⟨e, he, hae⟩
      obtain ⟨f, rfl⟩ := (hmemE e).mp he
      refine ⟨Φ (ι ((ggSpSigned_spReflAut p 3 k)⁻¹ f)), (hmemE _).mpr ⟨_, rfl⟩, ?_⟩
      have ha : a = (MulAut.conj (n k))⁻¹ * MulAut.conj (Φ (ι f)) * MulAut.conj (n k) := by
        rw [hae]
        group
      rw [ha, ← hwι']
      simp only [n, map_mul, map_inv]
  have hnformula : ∀ k (b : Fin 3 → μ),
      n k * φ b * (n k)⁻¹ = φ b * (φ (corTuple (CartanMatrix.C 3).transpose k (b k)))⁻¹ := by
    intro k b
    simp only [n, hφ_apply]
    rw [← map_inv, ← map_mul, ← map_mul, hw, refl_eq, root_rootInv hm hμ,
      rootInv_corTuple hm hμ, map_mul, map_inv, map_mul, map_inv]
  have hΘmem : ∀ f, MulAut.conj (Φ (ι f)) ∈ scalarA E := fun f =>
    ⟨Φ (ι f), (hmemE _).mpr ⟨f, rfl⟩, rfl⟩
  let Θ₀ : (Fin 3 → Multiplicative (ZMod p)) →* ↥(scalarA E) :=
    ((MulAut.conj : L' →* MulAut L').comp (Φ.comp ι)).codRestrict (scalarA E) hΘmem
  have hΘinj : Function.Injective Θ₀ := by
    rw [injective_iff_map_eq_one]
    intro f hf
    have h1 : MulAut.conj (Φ (ι f)) = 1 := congrArg Subtype.val hf
    have h2 : Φ (ι f) ∈ Subgroup.center L' := by
      have := mul_inv_mem_center_of_conj_eq (u := Φ (ι f)) (v := 1) (by rw [h1, map_one])
      simpa using this
    have h3 := hFZ _ (hcen _ h2)
    exact embPow_injective hζ (h3.trans (map_one _).symm)
  have hΘsurj : Function.Surjective Θ₀ := by
    rintro ⟨a, e, he, rfl⟩
    obtain ⟨f, rfl⟩ := (hmemE e).mp he
    exact ⟨f, rfl⟩
  let Θ : (Fin 3 → Multiplicative (ZMod p)) ≃* ↥(scalarA E) :=
    MulEquiv.ofBijective Θ₀ ⟨hΘinj, hΘsurj⟩
  have hΘ_apply : ∀ f, ((Θ f : ↥(scalarA E)) : MulAut L') = MulAut.conj (Φ (ι f)) :=
    fun _ => rfl
  have heq : ∀ k, ggConjAut (scalarA E) (hn k) =
      MulAut.congr Θ (ggSpSigned_spReflAut p 3 k) := by
    intro k
    apply MulEquiv.ext
    intro a
    obtain ⟨f, rfl⟩ := Θ.surjective a
    apply Subtype.ext
    have h1 : (MulAut.congr Θ (ggSpSigned_spReflAut p 3 k)) (Θ f) =
        Θ (ggSpSigned_spReflAut p 3 k f) := by
      simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rw [ggConjAut_apply, h1, hΘ_apply, hΘ_apply, ← hwι]
    simp only [n, map_mul, map_inv]
  have hsp : ∀ (mm : L') (hmm : MulAut.conj mm ∈
      Subgroup.normalizer ((scalarA E) : Set (MulAut L'))),
      SpCoord.IsSignedPerm ⇑((MulAut.congr Θ).symm (ggConjAut (scalarA E) hmm)) := by
    intro mm hmm
    obtain ⟨x, rfl⟩ := hΦ mm
    have hxf : ∀ f, ∃ f', x * ι f * x⁻¹ = ι f' := by
      intro f
      have h1 : MulAut.conj (Φ x) * MulAut.conj (Φ (ι f)) * (MulAut.conj (Φ x))⁻¹ ∈
          scalarA E := (Subgroup.mem_normalizer_iff.mp hmm _).mp (hΘmem f)
      obtain ⟨e, he, he'⟩ := h1
      obtain ⟨f', rfl⟩ := (hmemE e).mp he
      refine ⟨f', hlift x f f' ?_⟩
      rw [he']
      simp only [map_mul, map_inv]
    obtain ⟨π, ε, hε, hrel⟩ := hSN x hxf
    refine ⟨π, ε, hε, fun f i => ?_⟩
    set u := (MulAut.congr Θ).symm (ggConjAut (scalarA E) hmm) with hu
    have hΘu : Θ (u f) = ggConjAut (scalarA E) hmm (Θ f) := by
      rw [hu]
      simp only [MulAut.congr_symm_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    have hx' : x * ι f * x⁻¹ = ι (u f) := by
      apply hlift
      have h1 := congrArg Subtype.val hΘu
      rw [hΘ_apply, ggConjAut_apply, hΘ_apply] at h1
      rw [h1]
      simp only [map_mul, map_inv]
    exact hrel f (u f) hx' i
  obtain ⟨ρ, hρ, hρrange, hρsimple⟩ :=
    exists_rho_of_signedModel hp hp2 (by norm_num) Θ n hn heq hsp
  obtain ⟨B, hCB, hBC⟩ := exists_int_matrix_inverse_mod_C (m := m) (n := 3) (by norm_num) hm
  rw [hA]
  exact ggTorusTorData_of_rootCoordinates_tsc l φ hφinj (CartanMatrix.C 3) B hCB hBC hφZ Tsc
    hTsc_comm hTsc_tors hTsc_odd E hE ζ hζ.pow_eq_one (hζ.ne_one hp.one_lt) n hn hnformula hcent
    (CoxeterMatrix.B 3) ρ hρ hρrange hρsimple

end CFSG.StandardType.RelA5
