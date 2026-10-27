module

public import CFSG.LocalAnalysis.StandardType.GGNoTransvectionAutForm
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesFix

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace NoTvAut

section Power

variable {K : Type} [Field K] {p : ℕ} [NeZero p]

theorem exists_units_map_eq_pow {ζ : Kˣ} (hζo : orderOf ζ = p) (σ : K →+* K) :
    ∃ m : ℕ, ∀ c : Kˣ, c ^ p = 1 → Units.map σ.toMonoidHom c = c ^ m := by
  have hζ : ζ ^ p = 1 := hζo ▸ pow_orderOf_eq_one ζ
  have h1 : (Units.map σ.toMonoidHom ζ) ^ p = 1 := by rw [← map_pow, hζ, map_one]
  obtain ⟨m₀, hm₀⟩ := CFSG.RankThree.Chevalley.exists_pow_val_eq_of_pow_eq_one hζo h1
  refine ⟨m₀.val, fun c hc => ?_⟩
  obtain ⟨j, rfl⟩ := CFSG.RankThree.Chevalley.exists_pow_val_eq_of_pow_eq_one hζo hc
  rw [map_pow, ← hm₀, ← pow_mul, ← pow_mul, mul_comm]

omit [NeZero p] in
theorem coprime_of_units_map_eq_pow (hp : p.Prime) {ζ : Kˣ} (hζo : orderOf ζ = p) (σ : K →+* K)
    {m : ℕ} (hm : ∀ c : Kˣ, c ^ p = 1 → Units.map σ.toMonoidHom c = c ^ m) : Nat.Coprime m p := by
  have hζ : ζ ^ p = 1 := hζo ▸ pow_orderOf_eq_one ζ
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
  rintro ⟨j, rfl⟩
  have h1 := hm ζ hζ
  rw [pow_mul, hζ, one_pow] at h1
  have h2 : σ (ζ : K) = σ 1 := by
    rw [map_one]
    simpa using congrArg Units.val h1
  have h3 : ζ = 1 := Units.ext (σ.injective h2)
  rw [h3, orderOf_one] at hζo
  exact hp.one_lt.ne hζo

variable {τ : Tag}

omit [NeZero p] in
theorem units_map_entrywise_eq_pow (σ : K →+* K) {m : ℕ}
    (hm : ∀ c : Kˣ, c ^ p = 1 → Units.map σ.toMonoidHom c = c ^ m) {v : ModGL τ K}
    (hv : v ∈ ExcFrames.splitPow τ K p) : Units.map (entrywiseHom σ) v = v ^ m := by
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hv.1
  have hbp : b ^ p = 1 :=
    rootDiagUnit_injective (by rw [← rootDiagUnit_pow, hv.2, rootDiagUnit_one])
  rw [rootDiagUnit_pow]
  refine Units.ext ?_
  change entrywise σ (rootDiag b) = rootDiag (b ^ m)
  rw [entrywise_rootDiag]
  congr 1
  funext i
  rw [hm (b i) (by simpa using congrFun hbp i), Pi.pow_apply]

theorem frameDiag_nsmul (ζ : Kˣ) (hζ : ζ ^ p = 1) (s : Fin τ.rank → ZMod p) (m : ℕ) :
    ExcFrames.frameDiag (τ := τ) ζ hζ (m • s) = ExcFrames.frameDiag ζ hζ s ^ m := by
  induction m with
  | zero => rw [zero_nsmul, pow_zero, ExcFrames.frameDiag_zero]
  | succ m ih => rw [succ_nsmul, ExcFrames.frameDiag_add, ih, pow_succ]

theorem frameDiag_mem'
    (hfullp : ∀ b : Fin τ.rank → Kˣ, (∀ i, b i ^ p = 1) → rootDiagUnit τ b ∈ torusGroup τ K)
    (ζ : Kˣ) (hζ : ζ ^ p = 1) (s : Fin τ.rank → ZMod p) :
    ExcFrames.frameDiag (τ := τ) ζ hζ s ∈ ExcFrames.splitPow τ K p := by
  refine ⟨?_, ExcFrames.frameDiag_pow ζ hζ s⟩
  show rootDiagUnit τ (TableBExc.E6Three.zetaVec ζ hζ (ExcFrames.frameCoord τ p s)) ∈
    torusGroup τ K
  exact hfullp _ fun i => by
    rw [TableBExc.E6Three.zetaVec_apply, ← pow_mul, mul_comm, pow_mul, hζ, one_pow]

@[expose] noncomputable def frameHom'
    (hfullp : ∀ b : Fin τ.rank → Kˣ, (∀ i, b i ^ p = 1) → rootDiagUnit τ b ∈ torusGroup τ K)
    (ζ : Kˣ) (hζ : ζ ^ p = 1) (k : adjointGroup τ K) :
    Multiplicative (Fin τ.rank → ZMod p) →* adjointGroup τ K where
  toFun s := k⁻¹ * ⟨ExcFrames.frameDiag ζ hζ (Multiplicative.toAdd s),
    CFSG.RankThree.CentralCover.torusGroup_le_adjointGroup (frameDiag_mem' hfullp ζ hζ _).1⟩ * k
  map_one' := by
    refine Subtype.ext ?_
    simp [ExcFrames.frameDiag_zero]
  map_mul' x y := by
    refine Subtype.ext ?_
    simp only [toAdd_mul, Subgroup.coe_mul, Subgroup.coe_inv, ExcFrames.frameDiag_add]
    group

end Power

section Frame

variable {τ : Tag} {L : Type} [Field L] [Finite L] {p : ℕ} [Fact p.Prime]


theorem exists_simFrame {G : Type} [Group G]
    (hfullp : ∀ b : Fin τ.rank → Lˣ, (∀ i, b i ^ p = 1) → rootDiagUnit τ b ∈ torusGroup τ L)
    (hdet : IsUnit ((τ.symmetrizedCartan.det : ℤ) : ZMod p)) {ζ : Lˣ} (hζo : orderOf ζ = p)
    (χ : adjointGroup τ L →* G) (hχ : Function.Injective χ) (k : adjointGroup τ L)
    {Bs : Subgroup G}
    (hBs : ∀ b, b ∈ Bs ↔ ∃ v ∈ TableBExc.torusPow τ L p, b = χ (k⁻¹ * v * k))
    (hnf : ∀ α : MulAut (adjointGroup τ L), ∃ (a : adjointGroup τ L) (σ : L ≃+* L),
      ∀ v ∈ TableBExc.torusPow τ L p, ((α ^ 2) v : ModGL τ L) =
        (a : ModGL τ L) * Units.map (entrywiseHom σ.toRingHom) (v : ModGL τ L) *
          (a : ModGL τ L)⁻¹) :
    ∃ ι : Multiplicative (Fin τ.rank → ZMod p) →* G, Function.Injective ι ∧ ι.range = Bs ∧
      ∀ g ∈ Subgroup.normalizer (χ.range : Set G), g ∈ Subgroup.normalizer (Bs : Set G) →
        ∃ (w : WeylGroup τ) (m : ℕ), ∀ s : Fin τ.rank → ZMod p,
          g ^ 2 * ι (Multiplicative.ofAdd s) * (g ^ 2)⁻¹ =
            ι (Multiplicative.ofAdd (TableBExc.torusAct τ p w (m • s))) := by
  classical
  have hp : p.Prime := Fact.out
  have : Finite (adjointGroup τ L) := generated_group_finite τ L
  have : NeZero p := ⟨hp.ne_zero⟩
  have hζ : ζ ^ p = 1 := hζo ▸ pow_orderOf_eq_one ζ
  set V := TableBExc.torusPow τ L p with hV
  set t : (Fin τ.rank → ZMod p) → adjointGroup τ L := fun s =>
    ⟨ExcFrames.frameDiag ζ hζ s, CFSG.RankThree.CentralCover.torusGroup_le_adjointGroup
      (frameDiag_mem' hfullp ζ hζ s).1⟩ with ht
  have htV : ∀ s, t s ∈ V := fun s =>
    ExcFrames.mem_torusPow_iff_coe.mpr (frameDiag_mem' hfullp ζ hζ s)
  refine ⟨χ.comp (frameHom' hfullp ζ hζ k), ?_, ?_, ?_⟩
  · intro x y hxy
    have h1 : k⁻¹ * t (Multiplicative.toAdd x) * k = k⁻¹ * t (Multiplicative.toAdd y) * k :=
      hχ hxy
    have h2 := mul_left_cancel (mul_right_cancel h1)
    exact Multiplicative.toAdd.injective
      (ExcFrames.frameDiag_injective hζo hζ hdet (congrArg Subtype.val h2))
  · ext b
    rw [hBs]
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨t (Multiplicative.toAdd s), htV _, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨s, hs⟩ := ExcFrames.exists_frameDiag_of_mem hζo hζ hdet
        (ExcFrames.mem_torusPow_iff_coe.mp hv)
      refine ⟨.ofAdd s, ?_⟩
      have htv : t s = v := Subtype.ext hs
      show χ (k⁻¹ * t s * k) = χ (k⁻¹ * v * k)
      rw [htv]
  · intro g hgN hgB
    obtain ⟨α, hα⟩ := ExcFrames.exists_inducedAut χ hχ hgN
    set α' : MulAut (adjointGroup τ L) := MulAut.conj k * α * MulAut.conj k⁻¹ with hα'
    have hα'apply : ∀ x, α' x = k * α (k⁻¹ * x * k) * k⁻¹ := fun x => by
      rw [hα', MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply, inv_inv]
    have hα'2 : ∀ x, (α' ^ 2) x = k * (α ^ 2) (k⁻¹ * x * k) * k⁻¹ := fun x => by
      have e : α' ^ 2 = MulAut.conj k * α ^ 2 * MulAut.conj k⁻¹ := by
        rw [hα', map_inv, conj_pow]
      rw [e, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply, inv_inv]
    have hα2 : ∀ x, χ ((α ^ 2) x) = g ^ 2 * χ x * (g ^ 2)⁻¹ := ExcFrames.inducedAut_pow χ hα 2
    have hα'V : ∀ v ∈ V, α' v ∈ V := by
      intro v hv
      have h1 : χ (k⁻¹ * v * k) ∈ Bs := (hBs _).mpr ⟨v, hv, rfl⟩
      have h2 : g * χ (k⁻¹ * v * k) * g⁻¹ ∈ Bs := (Subgroup.mem_normalizer_iff.mp hgB _).mp h1
      rw [← hα] at h2
      obtain ⟨v', hv', hv'eq⟩ := (hBs _).mp h2
      have h3 : α (k⁻¹ * v * k) = k⁻¹ * v' * k := hχ hv'eq
      have h4 : k * (k⁻¹ * v' * k) * k⁻¹ = v' := by group
      rw [hα'apply, h3, h4]
      exact hv'
    have hα'2V : ∀ v ∈ V, (α' ^ 2) v ∈ V := fun v hv => by
      rw [pow_two, MulAut.mul_apply]
      exact hα'V _ (hα'V v hv)
    obtain ⟨a, σ, haσ⟩ := hnf α'
    obtain ⟨m, hm⟩ := exists_units_map_eq_pow hζo σ.toRingHom
    have hmp := coprime_of_units_map_eq_pow hp hζo σ.toRingHom hm
    have hpw : ∀ v ∈ V, ((α' ^ 2) v : ModGL τ L) =
        (a : ModGL τ L) * (v : ModGL τ L) ^ m * (a : ModGL τ L)⁻¹ := by
      intro v hv
      rw [haσ v hv,
        units_map_entrywise_eq_pow σ.toRingHom hm (ExcFrames.mem_torusPow_iff_coe.mp hv)]
    obtain ⟨m', -, hm'⟩ := Nat.exists_mul_mod_eq_one_of_coprime hmp hp.one_lt
    have hroot : ∀ v ∈ V, ∃ v' ∈ V, v = v' ^ m := by
      intro v hv
      refine ⟨v ^ m', V.pow_mem hv m', ?_⟩
      rw [← pow_mul, mul_comm m' m, pow_eq_pow_mod (m * m') (hv.2 : v ^ p = 1), hm', pow_one]
    have haV : ∀ v ∈ V, a * v * a⁻¹ ∈ V := by
      intro v hv
      obtain ⟨v', hv', rfl⟩ := hroot v hv
      have h1 : (α' ^ 2) v' = a * v' ^ m * a⁻¹ := Subtype.ext (by
        rw [hpw v' hv', Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_inv])
      rw [← h1]
      exact hα'2V v' hv'
    have hnormV : ∀ x : adjointGroup τ L, x ∈ V ↔ a * x * a⁻¹ ∈ V := by
      intro x
      refine ⟨haV x, fun hx => ?_⟩
      have hinj : Function.Injective (fun v : V => (⟨a * v * a⁻¹, haV v v.2⟩ : V)) := by
        intro v w hvw
        have h1 : a * (v : adjointGroup τ L) * a⁻¹ = a * w * a⁻¹ := congrArg Subtype.val hvw
        exact Subtype.ext (mul_left_cancel (mul_right_cancel h1))
      obtain ⟨v, hv⟩ := (Finite.injective_iff_surjective.mp hinj) ⟨_, hx⟩
      have h1 : a * (v : adjointGroup τ L) * a⁻¹ = a * x * a⁻¹ := congrArg Subtype.val hv
      have h2 : (v : adjointGroup τ L) = x := mul_left_cancel (mul_right_cancel h1)
      rw [← h2]
      exact v.2
    obtain ⟨w, hw⟩ := ExcFrames.exists_weyl_of_normalizes hnormV
    refine ⟨w, m, fun s => ?_⟩
    have h1 : (α' ^ 2) (t s) = t (TableBExc.torusAct τ p w (m • s)) := by
      refine Subtype.ext ?_
      rw [hpw _ (htV s)]
      show (a : ModGL τ L) * ExcFrames.frameDiag ζ hζ s ^ m * (a : ModGL τ L)⁻¹ =
        ExcFrames.frameDiag ζ hζ (TableBExc.torusAct τ p w (m • s))
      rw [← frameDiag_nsmul, hw _ (frameDiag_mem' hfullp ζ hζ _),
        ExcFrames.canonicalRep_conj_frameDiag]
    have h2 : (α ^ 2) (k⁻¹ * t s * k) = k⁻¹ * (α' ^ 2) (t s) * k := by
      rw [hα'2]
      group
    show g ^ 2 * χ (k⁻¹ * t s * k) * (g ^ 2)⁻¹ =
      χ (k⁻¹ * t (TableBExc.torusAct τ p w (m • s)) * k)
    rw [← hα2, h2, h1]

end Frame

end NoTvAut

end CFSG.StandardType

end
