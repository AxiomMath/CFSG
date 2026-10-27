module

public import CFSG.Quasithin.EmptyFaithful.S152He17B
public import CFSG.Quasithin.EmptyFaithful.S152He16D
public import CFSG.Quasithin.EmptyFaithful.S152He17A

public section

namespace CFSG.Quasithin.He17

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.He9
  CFSG.Quasithin.He16
open scoped commutatorElement Pointwise

theorem iterate_fixed_of_pow_five {X : Type*} (g : X → X) (hg : ∀ x, g^[5] x = x) (s : Finset X)
    (hs : ∀ x ∈ s, g x ∈ s) (hcard : s.card ≤ 4) : ∀ x ∈ s, g x = x := by
  classical
  intro x hx
  have hdvd := (show Function.IsPeriodicPt g 5 x from hg x).minimalPeriod_dvd
  rcases (Nat.dvd_prime Nat.prime_five).mp hdvd with h1 | h5
  · exact Function.minimalPeriod_eq_one_iff_isFixedPt.mp h1
  · exfalso
    have hinj : Set.InjOn (fun i => g^[i] x) (Set.Iio 5) := by
      have := (Function.iterate_injOn_Iio_minimalPeriod (f := g) (x := x))
      rwa [h5] at this
    have hmem : ∀ i, g^[i] x ∈ s := by
      intro i
      induction i with
      | zero => exact hx
      | succ i ih => rw [Function.iterate_succ_apply']; exact hs _ ih
    have hsub : (Finset.range 5).image (fun i => g^[i] x) ⊆ s := by
      intro z hz
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
      exact hmem i
    have hc : ((Finset.range 5).image (fun i => g^[i] x)).card = 5 := by
      rw [Finset.card_image_of_injOn]
      · simp
      · intro i hi j hj hij
        exact hinj (by simpa using hi) (by simpa using hj) hij
    have := Finset.card_le_card hsub
    omega

theorem eq_one_of_stabilizes_partition {α : Type*} [DecidableEq α] (σ : Equiv.Perm α)
    (hσ : σ ^ 5 = 1) (P : Finset (Finset α)) (hP : ∀ B ∈ P, B.image σ ∈ P)
    (hcover : ∀ x, ∃ B ∈ P, x ∈ B) (hPc : P.card ≤ 4) (hBc : ∀ B ∈ P, B.card ≤ 4) : σ = 1 := by
  have hit : ∀ (n : ℕ) (B : Finset α), (fun B : Finset α => B.image σ)^[n] B = B.image (σ^[n]) := by
    intro n
    induction n with
    | zero => intro B; simp
    | succ n ih =>
      intro B
      rw [Function.iterate_succ_apply, ih, Finset.image_image, Function.iterate_succ]
  have hσ5 : ∀ x, σ^[5] x = x := by
    intro x
    rw [Equiv.Perm.iterate_eq_pow, hσ]
    rfl
  have hblocks : ∀ B ∈ P, B.image σ = B := by
    refine iterate_fixed_of_pow_five (fun B : Finset α => B.image σ) (fun B => ?_) P hP hPc
    rw [hit]
    have : σ^[5] = id := funext hσ5
    rw [this, Finset.image_id]
  ext x
  obtain ⟨B, hB, hxB⟩ := hcover x
  have hinv : ∀ z ∈ B, σ z ∈ B := by
    intro z hz
    have : σ z ∈ B.image σ := Finset.mem_image_of_mem σ hz
    rwa [hblocks B hB] at this
  have := iterate_fixed_of_pow_five (⇑σ) hσ5 B hinv (hBc B hB) x hxB
  simpa using this

theorem not_stabilizes_partition {sizes : Multiset ℕ} (hs : ∀ n ∈ sizes, n ≤ 4)
    (hc : Multiset.card sizes ≤ 4) {P : Finset (Finset (Fin 7))} (hP : IsPartitionOfType P sizes)
    {σ : Equiv.Perm (Fin 7)} (hσ : orderOf σ = 5)
    (hstab : σ ∈ MulAction.stabilizer (Equiv.Perm (Fin 7)) P) : False := by
  obtain ⟨-, -, hcov, hsz⟩ := hP
  have hst : σ • P = P := MulAction.mem_stabilizer_iff.mp hstab
  have hσ5 : σ ^ 5 = 1 := hσ ▸ pow_orderOf_eq_one σ
  have h1 : σ = 1 := by
    refine eq_one_of_stabilizes_partition σ hσ5 P (fun B hB => ?_) (fun x => ?_) ?_ (fun B hB => ?_)
    · have : σ • B ∈ σ • P := Finset.smul_mem_smul_finset hB
      rw [hst] at this
      simpa [Finset.smul_finset_def, Equiv.Perm.smul_def] using this
    · have : x ∈ P.biUnion id := by rw [hcov]; exact Finset.mem_univ x
      obtain ⟨B, hB, hxB⟩ := Finset.mem_biUnion.mp this
      exact ⟨B, hB, hxB⟩
    · have := congrArg Multiset.card hsz
      rw [Multiset.card_map] at this
      exact (Finset.card_def P ▸ this ▸ hc)
    · have : B.card ∈ P.val.map Finset.card := Multiset.mem_map_of_mem _ hB
      rw [hsz] at this
      exact hs _ this
  rw [h1, orderOf_one] at hσ
  omega

variable {G : Type} [Group G] [Finite G]

theorem five_dvd_card_Y {T Mc M H K₁ K₂ : Subgroup G} {π : ↥H →* W5}
    (c : Ctx15204 T Mc M H K₁ K₂ π) : 5 ∣ Nat.card (yOf152 T Mc M) := by
  have hmul := Subgroup.relIndex_mul_card (H := pCoreOf 2 (yOf152 T Mc M)) (K := yOf152 T Mc M)
  rw [c.y.relIndex_five, inf_eq_left.mpr (pCoreOf_le 2 _)] at hmul
  exact Dvd.intro _ hmul

theorem Y_le_inf {T Mc M H K₁ K₂ : Subgroup G} {π : ↥H →* W5} (c : Ctx15204 T Mc M H K₁ K₂ π)
    {Lc : Subgroup G} (hYL : yOf152 T Mc M ≤ Lc) :
    yOf152 T Mc M ≤ (M ⊓ g0Of T Mc M K₁) ⊓ Lc :=
  le_inf (le_inf c.y.hYM Y_le_G₀) hYL

theorem not_five_dvd_of_index {m a r s : ℕ} (hr : ¬ 5 ∣ r) (h : m * (5 * s) = 2 ^ a * (5 * r)) :
    ¬ 5 ∣ m := by
  intro h5
  have h1 : m * s = 2 ^ a * r := by
    apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 5)
    linarith
  have : 5 ∣ 2 ^ a * r := h1 ▸ Dvd.dvd.mul_right h5 s
  rcases (Nat.Prime.dvd_mul Nat.prime_five).mp this with h2 | h2
  · exact absurd (Nat.prime_five.dvd_of_dvd_pow h2) (by norm_num)
  · exact hr h2

theorem false_of_hatA6 {T Mc M H K₁ K₂ : Subgroup G} {π : ↥H →* W5}
    (c : Ctx15204 T Mc M H K₁ K₂ π) {Lc : Subgroup G} (hYL : yOf152 T Mc M ≤ Lc)
    (hA : IsHatA6Block Lc) (hidx : (M ⊓ g0Of T Mc M K₁).relIndex Lc = 15) : False := by
  have h5 : 5 ∣ Nat.card ↥((M ⊓ g0Of T Mc M K₁) ⊓ Lc) :=
    (five_dvd_card_Y c).trans (Subgroup.card_dvd_of_le (Y_le_inf c hYL))
  obtain ⟨-, ⟨-, hZ3, ⟨e⟩⟩, -⟩ := hA
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 (CFSG.pCore_isPGroup (p := 2) (G := ↥Lc))
  have hA6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  have hq : Nat.card (↥Lc ⧸ CFSG.pCore 2 ↥Lc) = 1080 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (Subgroup.center (↥Lc ⧸ CFSG.pCore 2 ↥Lc))
    rw [hZ3, Nat.card_congr e.toEquiv, hA6] at h1
    exact h1
  have hLc : Nat.card ↥Lc = 2 ^ a * 1080 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥Lc)
    rw [hq, ha] at h1
    rw [h1]; ring
  have hmul := Subgroup.relIndex_mul_card (H := M ⊓ g0Of T Mc M K₁) (K := Lc)
  rw [hidx, hLc] at hmul
  exact not_five_dvd_of_index (r := 216) (s := 3) (by norm_num) (by linarith) h5

theorem false_of_excA7 {T Mc M H K₁ K₂ : Subgroup G} {π : ↥H →* W5}
    (c : Ctx15204 T Mc M H K₁ K₂ π) {Lc : Subgroup G} (hYL : yOf152 T Mc M ≤ Lc)
    (hA : IsExcA7Block Lc) (hidx : (M ⊓ g0Of T Mc M K₁).relIndex Lc = 35) : False := by
  have h5 : 5 ∣ Nat.card ↥((M ⊓ g0Of T Mc M K₁) ⊓ Lc) :=
    (five_dvd_card_Y c).trans (Subgroup.card_dvd_of_le (Y_le_inf c hYL))
  obtain ⟨-, ⟨α, hα, hker⟩, -⟩ := hA
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 (CFSG.pCore_isPGroup (p := 2) (G := ↥Lc))
  have hq : Nat.card (↥Lc ⧸ CFSG.pCore 2 ↥Lc) = 2520 := by
    let e : (↥Lc ⧸ CFSG.pCore 2 ↥Lc) ≃* alternatingGroup (Fin 7) :=
      (QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivOfSurjective α hα)
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  have hLc : Nat.card ↥Lc = 2 ^ a * 2520 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥Lc)
    rw [hq, ha] at h1
    rw [h1]; ring
  have hmul := Subgroup.relIndex_mul_card (H := M ⊓ g0Of T Mc M K₁) (K := Lc)
  rw [hidx, hLc] at hmul
  exact not_five_dvd_of_index (r := 504) (s := 7) (by norm_num) (by linarith) h5

theorem false_of_partition {T Mc M H K₁ K₂ : Subgroup G} {π : ↥H →* W5}
    (c : Ctx15204 T Mc M H K₁ K₂ π) {Lc : Subgroup G} (hYL : yOf152 T Mc M ≤ Lc) {V : Subgroup G}
    {y : G} (hyY : y ∈ yOf152 T Mc M) (hyN : y ∈ Subgroup.normalizer (V : Set G))
    (hy5 : orderOf (conjAct V ⟨y, hyN⟩) = 5)
    (e : ↥(autOn (Lc ⊔ rOf T Mc M K₁) V) ≃* Equiv.Perm (Fin 7)) {sizes : Multiset ℕ}
    (hs : ∀ n ∈ sizes, n ≤ 4) (hcard : Multiset.card sizes ≤ 4) {P : Finset (Finset (Fin 7))}
    (hP : IsPartitionOfType P sizes)
    (hmap : ((autOn ((M ⊓ g0Of T Mc M K₁) ⊓ Lc) V).subgroupOf
        (autOn (Lc ⊔ rOf T Mc M K₁) V)).map e.toMonoidHom =
      MulAction.stabilizer (Equiv.Perm (Fin 7)) P ⊓ alternatingGroup (Fin 7)) : False := by
  have hyM : y ∈ (M ⊓ g0Of T Mc M K₁) ⊓ Lc := Y_le_inf c hYL hyY
  have ha1 : conjAct V ⟨y, hyN⟩ ∈ autOn ((M ⊓ g0Of T Mc M K₁) ⊓ Lc) V :=
    mem_autOn_iff_exists.mpr ⟨y, hyN, hyM, rfl⟩
  have ha2 : conjAct V ⟨y, hyN⟩ ∈ autOn (Lc ⊔ rOf T Mc M K₁) V :=
    mem_autOn_iff_exists.mpr ⟨y, hyN, Subgroup.mem_sup_left (hYL hyY), rfl⟩
  have hmem : (⟨conjAct V ⟨y, hyN⟩, ha2⟩ : ↥(autOn (Lc ⊔ rOf T Mc M K₁) V)) ∈
      (autOn ((M ⊓ g0Of T Mc M K₁) ⊓ Lc) V).subgroupOf (autOn (Lc ⊔ rOf T Mc M K₁) V) := ha1
  have he : e ⟨conjAct V ⟨y, hyN⟩, ha2⟩ ∈
      MulAction.stabilizer (Equiv.Perm (Fin 7)) P ⊓ alternatingGroup (Fin 7) :=
    hmap ▸ Subgroup.mem_map_of_mem _ hmem
  have hord : orderOf (e ⟨conjAct V ⟨y, hyN⟩, ha2⟩) = 5 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hy5]
  exact not_stabilizes_partition hs hcard hP hord (Subgroup.mem_inf.mp he).1


@[expose] def C27Rest2 (R M K V : Subgroup G) : Prop :=
  ((∃ (n : ℕ) (α : ↥K →* alternatingGroup (Fin n)), 5 ≤ n ∧ n ≤ 8 ∧ IsShort2 K ∧
      IsAltBlockTypeWith K n α ∧
      ∃ t : G, t ∈ R ∧ ∃ htV : t ∈ Subgroup.normalizer (V : Set G),
        autOn R V = Subgroup.zpowers (conjAct V ⟨t, htV⟩) ∧
        orderOf (conjAct V ⟨t, htV⟩) = 2 ∧
        ∃ σ : Equiv.Perm (Fin n), σ.IsSwap ∧
          ∀ (k : G) (hk : k ∈ K) (hk' : t * k * t⁻¹ ∈ K),
            ((α ⟨t * k * t⁻¹, hk'⟩ : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) =
              σ * (α ⟨k, hk⟩ : Equiv.Perm (Fin n)) * σ⁻¹) ∧
    autOn (M ⊓ K) V = autOn K V ⊓ Subgroup.centralizer (autOn R V : Set (MulAut ↥V))) ∨
  ((IsAltBlockType K 6 ∨ IsSp4Block K) ∧
    IsMaxParabolic2 (autOn K V) (autOn (M ⊓ K) V)) ∨
  (CFSG.Quasithin.IsG2Block K ∧ IsG2Two ↥(autOn (K ⊔ R) V) ∧
    IsMaxParabolic2 (autOn (K ⊔ R) V) (autOn (M ⊓ K) V ⊔ autOn R V)) ∨
  ((∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F), 1 ≤ n ∧ Fintype.card F = 2 ^ n ∧
      Nonempty (↥(autOn K V) ≃* ↥(StatedSL 3 F))) ∧
    IsMaxParabolic2 (autOn K V) (autOn (M ⊓ K) V) ∧ IsMSPair (K ⊔ R) R) ∨
  ((Nonempty (↥(autOn K V) ≃* ↥(StatedSL 4 (ZMod 2))) ∨
      Nonempty (↥(autOn K V) ≃* ↥(StatedSL 5 (ZMod 2)))) ∧
    IsParabolic2 (autOn K V) (autOn (M ⊓ K) V) ∧ ¬ IsBorelIn (autOn K V) (autOn (M ⊓ K) V))

@[expose] def Input15204QuasiRest2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M H K₁ K₂ : Subgroup G) (π : ↥H →* W5)
    (c : Ctx15204 T Mc M H K₁ K₂ π) (Lc : Subgroup G), Tail15204 c Lc →
    yOf152 T Mc M ≤ Lc → ¬ IsSylowTwoOf (rOf T Mc M K₁) (rOf T Mc M K₁ ⊔ Lc) →
    CFSG.IsQuasisimple ↥(modO2Image (g0Of T Mc M K₁) Lc) →
    C27Rest2 (rOf T Mc M K₁) (M ⊓ g0Of T Mc M K₁) Lc
      (omegaOneCenterOf (pCoreOf 2 (Lc ⊔ rOf T Mc M K₁))) → False

theorem input15204BranchBQuasi_of_rest2
    (hC27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G) (h : Input15204QuasiRest2) :
    Input15204BranchBQuasi := by
  intro G _ _ T Mc M H K₁ K₂ π c Lc tail hYL hnot hq
  obtain ⟨y, hyY, hyN, hy5⟩ := exists_five_element (hC27 G) c tail hYL hq
  have hLG : Lc ≤ g0Of T Mc M K₁ := le_of_mem_cComp tail.comp
  have hNG : g0Of T Mc M K₁ ≤ Subgroup.normalizer (Lc : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLG).1 tail.normal
  have hRN : rOf T Mc M K₁ ≤ Subgroup.normalizer (Lc : Set G) := tail.hyp.radical.1.trans hNG
  obtain ⟨-, -, h3⟩ := hC27 G (g0Of T Mc M K₁) (rOf T Mc M K₁) (M ⊓ g0Of T Mc M K₁) Lc _
    tail.hyp tail.comp (isQuasisimple_quot tail.comp hq)
    (CFSG.Quasithin.CT.CharTwo.of_normal tail.charTwo hLG tail.normal) tail.not_le hRN rfl
  have hrest := h G T Mc M H K₁ K₂ π c Lc tail hYL hnot hq
  rcases h3 with ⟨hblk, ha⟩ | hb | hc3 | hd | he | hf | hg | hh
  · rcases ha with ⟨hlin, -⟩ | ⟨hA5, -⟩ | ⟨hA7, -, e, P, hP, hmap⟩ | ⟨hA7, -, e, P, hP, hmap⟩
    · exact false_of_chi0 c tail hYL ⟨hblk.1, Or.inl hlin⟩
    · exact false_of_chi0 c tail hYL ⟨hblk.1, Or.inr (Or.inr hA5)⟩
    · exact false_of_partition c hYL hyY hyN hy5 e (sizes := {4, 3}) (by decide) (by decide) hP hmap
    · exact false_of_partition c hYL hyY hyN hy5 e (sizes := {2, 2, 2, 1}) (by decide) (by decide)
        hP hmap
  · exact hrest (Or.inl hb)
  · exact false_of_hatA6 c hYL hc3.1 hc3.2.1
  · exact false_of_excA7 c hYL hd.1 hd.2
  · exact hrest (Or.inr (Or.inl he))
  · exact hrest (Or.inr (Or.inr (Or.inl hf)))
  · exact hrest (Or.inr (Or.inr (Or.inr (Or.inl hg))))
  · exact hrest (Or.inr (Or.inr (Or.inr (Or.inr hh))))

end CFSG.Quasithin.He17
