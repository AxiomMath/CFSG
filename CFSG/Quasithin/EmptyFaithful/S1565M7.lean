module

public import CFSG.Quasithin.EmptyFaithful.S1565M6
public import CFSG.Quasithin.Background.F918P0

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank Matrix

section Natural

variable {W : Type} [CommGroup W] {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]

theorem natural_realizes_injective (Γ : Subgroup (GL ι F)) {H : Subgroup (MulAut W)} {U Z : Subgroup W}
    {π : Γ →* ↥H} (hR : (FFModel.nat Γ).RealizesVia H U Z π) : Function.Injective π := by
  obtain ⟨-, -, -, hUinv, -, -, -, β, hβs, hβker, hβact⟩ := hR
  rw [injective_iff_map_eq_one]
  intro γ hγ
  have hfix : ∀ m : Multiplicative (ι → F), natAct Γ γ m = m := by
    intro m
    obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk (⟨m, trivial⟩ : ↥(FFModel.nat Γ).sec))
    have hU' : ((π γ : ↥H) : MulAut W) (u : W) ∈ U := hUinv (π γ) u u.2
    have hm' : (FFModel.nat Γ).act γ m ∈ (FFModel.nat Γ).sec := trivial
    have h1 := hβact γ u ⟨m, trivial⟩ hU' hm' hu
    have hπ1 : ∀ w : W, ((π γ : ↥H) : MulAut W) w = w := by
      intro w
      rw [hγ]
      rfl
    have h2 : (⟨((π γ : ↥H) : MulAut W) (u : W), hU'⟩ : ↥U) = u := Subtype.ext (hπ1 _)
    have h1' : β u = QuotientGroup.mk (⟨(FFModel.nat Γ).act γ m, hm'⟩ : ↥(FFModel.nat Γ).sec) := by
      exact (congrArg β h2).symm.trans h1
    have hmk := h1'.symm.trans hu
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at hmk
    have h0 := Subgroup.mem_bot.mp hmk
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h0
    exact inv_mul_eq_one.mp h0
  have hM : ((γ : GL ι F) : Matrix ι ι F) = 1 := by
    apply Matrix.ext_of_mulVec_single
    intro i
    have := congrArg Multiplicative.toAdd (hfix (Multiplicative.ofAdd (Pi.single i 1)))
    rw [Matrix.one_mulVec]
    exact this
  exact Subtype.ext (Units.ext hM)

theorem natural_regular_of_noFixedVec (Γ : Subgroup (GL ι F)) {H : Subgroup (MulAut W)}
    {U Z : Subgroup W} {π : Γ →* ↥H} (hR : (FFModel.nat Γ).RealizesVia H U Z π) (g : Γ)
    (hg : NoFixedVec (g : GL ι F)) :
    ∀ u ∈ U, ((π g : ↥H) : MulAut W) u * u⁻¹ ∈ Z → u ∈ Z := by
  intro u hu hb
  obtain ⟨-, hZU, -, hUinv, -, -, -, β, -, hβker, hβact⟩ := hR
  set u' : ↥U := ⟨u, hu⟩ with hu'
  have hbU : ((π g : ↥H) : MulAut W) u ∈ U := hUinv (π g) u hu
  have hβeq : β ⟨((π g : ↥H) : MulAut W) u, hbU⟩ = β u' := by
    have h1 : β (⟨((π g : ↥H) : MulAut W) u, hbU⟩ * u'⁻¹) = 1 := by
      rw [hβker]
      exact hb
    rw [map_mul, map_inv, mul_inv_eq_one] at h1
    exact h1
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β u')
  have hm' : (FFModel.nat Γ).act g m.1 ∈ (FFModel.nat Γ).sec := trivial
  have hact := hβact g u' m hbU hm' hm.symm
  have hmk : (QuotientGroup.mk ⟨(FFModel.nat Γ).act g m.1, hm'⟩ :
      ↥(FFModel.nat Γ).sec ⧸ (FFModel.nat Γ).ker.subgroupOf (FFModel.nat Γ).sec) =
      QuotientGroup.mk m := hact.symm.trans (hβeq.trans hm.symm)
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at hmk
  have h1 : natAct Γ g (m.1 : Multiplicative (ι → F)) = (m.1 : Multiplicative (ι → F)) := by
    have h0 := Subgroup.mem_bot.mp hmk
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h0
    exact inv_mul_eq_one.mp h0
  set x : ι → F := Multiplicative.toAdd (m.1 : Multiplicative (ι → F)) with hx
  have h2 : ((g : GL ι F) : Matrix ι ι F).mulVec x = x := congrArg Multiplicative.toAdd h1
  have h5 : x = 0 := hg x h2
  have h6 : m = 1 := Subtype.ext (by
    apply Multiplicative.toAdd.injective
    exact h5)
  have h7 : β u' = 1 := by rw [← hm, h6]; rfl
  exact (hβker u').mp h7

theorem natural_twist_element (Γ : Subgroup (GL ι F)) [Finite Γ]
    (hReg : ∀ (Q : Sylow 2 Γ) (α : Γ ≃* Γ),
      (∀ x, x ∈ (Q : Subgroup Γ) ↔ α x ∈ (Q : Subgroup Γ)) →
      ∃ c : Γ, c ∈ Subgroup.normalizer ((Q : Subgroup Γ) : Set Γ) ∧ ∃ m : ℕ, Odd m ∧ c ^ m = 1 ∧
        NoFixedVec (c : GL ι F) ∧ NoFixedVec ((α c : Γ) : GL ι F))
    {H : Subgroup (MulAut W)} {U Z : Subgroup W} {π : Γ →* ↥H}
    (hR : (FFModel.nat Γ).RealizesVia H U Z π) (S : Sylow 2 ↥H) (δ : ↥H ≃* ↥H)
    (hδ : ∀ h, h ∈ (S : Subgroup ↥H) ↔ δ h ∈ (S : Subgroup ↥H)) :
    ∃ b ∈ Subgroup.normalizer ((S : Subgroup ↥H) : Set ↥H), ∃ m : ℕ, Odd m ∧ b ^ m = 1 ∧
      (∀ u ∈ U, ((b : MulAut W) u) * u⁻¹ ∈ Z → u ∈ Z) ∧
      (∀ u ∈ U, (((δ b : ↥H) : MulAut W) u) * u⁻¹ ∈ Z → u ∈ Z) := by
  have hinj := natural_realizes_injective Γ hR
  have hsurj : Function.Surjective π := hR.1
  let e : Γ ≃* ↥H := MulEquiv.ofBijective π ⟨hinj, hsurj⟩
  have he : ∀ x, e x = π x := fun x => rfl
  obtain ⟨S₁, hS₁⟩ := Sylow.mapSurjective_surjective hsurj 2 S
  have hS₁S : (S : Subgroup ↥H) = (S₁ : Subgroup Γ).map π := by
    rw [← hS₁, Sylow.coe_mapSurjective]
  have hS₁mem : ∀ x : Γ, x ∈ (S₁ : Subgroup Γ) ↔ π x ∈ (S : Subgroup ↥H) := by
    intro x
    rw [hS₁S]
    exact (Subgroup.mem_map_iff_mem hinj).symm
  let α' : Γ ≃* Γ := e.trans (δ.trans e.symm)
  have hπα : ∀ x, π (α' x) = δ (π x) := by
    intro x
    rw [← he, ← he]
    simp [α']
  have hα' : ∀ x, x ∈ (S₁ : Subgroup Γ) ↔ α' x ∈ (S₁ : Subgroup Γ) := by
    intro x
    rw [hS₁mem, hS₁mem, hπα]
    exact hδ (π x)
  obtain ⟨c, hcN, m, hm, hcm, hr0, hr1⟩ := hReg S₁ α' hα'
  refine ⟨π c, ?_, m, hm, by rw [← map_pow, hcm, map_one], ?_, ?_⟩
  · have h1 := Subgroup.le_normalizer_map π ⟨c, hcN, rfl⟩
    rw [hS₁S]
    exact h1
  · exact natural_regular_of_noFixedVec Γ hR c hr0
  · rw [← hπα]
    exact natural_regular_of_noFixedVec Γ hR (α' c) hr1

end Natural

section Sum

variable {W : Type} [CommGroup W]

theorem regular_of_sumMod {C A B : Subgroup W} (hsum : IsSumMod C A B ⊤) {b : MulAut W}
    (hA : ∀ a ∈ A, b a ∈ A) (hB : ∀ x ∈ B, b x ∈ B) (hC : ∀ c ∈ C, b c = c)
    (hRA : ∀ a ∈ A, b a * a⁻¹ ∈ C → a ∈ C) (hRB : ∀ x ∈ B, b x * x⁻¹ ∈ C → x ∈ C) :
    ∀ w : W, b w * w⁻¹ ∈ C → w ∈ C := by
  intro w hw
  obtain ⟨htot, hint⟩ := hsum
  have hwtop : w ∈ (⊤ : Subgroup W) := trivial
  rw [htot] at hwtop
  obtain ⟨y, hy, c, hc, rfl⟩ := Subgroup.mem_sup.mp hwtop
  obtain ⟨a, ha, x, hx, rfl⟩ := Subgroup.mem_sup.mp hy
  have h1 : b (a * x * c) * (a * x * c)⁻¹ = (b a * a⁻¹) * (b x * x⁻¹) := by
    rw [map_mul, map_mul, hC c hc]
    simp only [_root_.mul_inv_rev]
    rw [mul_comm c⁻¹ (x⁻¹ * a⁻¹)]
    calc b a * b x * c * (x⁻¹ * a⁻¹ * c⁻¹)
        = b a * b x * (x⁻¹ * a⁻¹) * (c * c⁻¹) := by ac_rfl
      _ = (b a * a⁻¹) * (b x * x⁻¹) := by rw [mul_inv_cancel, mul_one]; ac_rfl
  rw [h1] at hw
  set p := b a * a⁻¹ with hp
  set q := b x * x⁻¹ with hq
  have hpA : p ∈ A := A.mul_mem (hA a ha) (A.inv_mem ha)
  have hqB : q ∈ B := B.mul_mem (hB x hx) (B.inv_mem hx)
  have hpC : p ∈ C := by
    have h2 : p ∈ B ⊔ C := by
      have : p = (p * q) * q⁻¹ := by rw [mul_inv_cancel_right]
      rw [this]
      exact (B ⊔ C).mul_mem (Subgroup.mem_sup_right hw) ((B ⊔ C).inv_mem (Subgroup.mem_sup_left hqB))
    exact hint ⟨Subgroup.mem_sup_left hpA, h2⟩
  have hqC : q ∈ C := by
    have h2 : q ∈ A ⊔ C := by
      have : q = p⁻¹ * (p * q) := by rw [inv_mul_cancel_left]
      rw [this]
      exact (A ⊔ C).mul_mem ((A ⊔ C).inv_mem (Subgroup.mem_sup_left hpA)) (Subgroup.mem_sup_right hw)
    exact hint ⟨h2, Subgroup.mem_sup_left hqB⟩
  exact C.mul_mem (C.mul_mem (hRA a ha hpC) (hRB x hx hqC)) hc

end Sum

section Twist

variable {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}

private def conjInvL (τ : MulAut W) (hτ : τ ∈ Subgroup.normalizer (L : Set (MulAut W))) :
    ↥L ≃* ↥L where
  toFun x := ⟨τ⁻¹ * (x : MulAut W) * τ, by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hτ) (x : MulAut W)).mp x.2
    simpa using this⟩
  invFun x := ⟨τ * (x : MulAut W) * τ⁻¹, (Subgroup.mem_normalizer_iff.mp hτ (x : MulAut W)).mp x.2⟩
  left_inv x := by
    apply Subtype.ext
    show τ * (τ⁻¹ * (x : MulAut W) * τ) * τ⁻¹ = x
    group
  right_inv x := by
    apply Subtype.ext
    show τ⁻¹ * (τ * (x : MulAut W) * τ⁻¹) * τ = x
    group
  map_mul' x y := by
    apply Subtype.ext
    show τ⁻¹ * ((x : MulAut W) * (y : MulAut W)) * τ = τ⁻¹ * (x : MulAut W) * τ * (τ⁻¹ * (y : MulAut W) * τ)
    group

private theorem conjInvL_coe (τ : MulAut W) (hτ : τ ∈ Subgroup.normalizer (L : Set (MulAut W)))
    (x : ↥L) : ((conjInvL τ hτ x : ↥L) : MulAut W) = τ⁻¹ * (x : MulAut W) * τ := rfl

private theorem fixV_of_normalizer {Mp : Subgroup (MulAut W)} {τ : MulAut W}
    (hτ : τ ∈ Subgroup.normalizer (Mp : Set (MulAut W))) {c : W} (hc : c ∈ fixV Mp) :
    τ c ∈ fixV Mp :=
  CFSG.Quasithin.fixV_apply_mem_of_mem_normalizer hτ hc

private theorem exists_adjust [Finite ↥L] (S : Sylow 2 ↥L) {t : MulAut W}
    (ht : t ∈ Subgroup.normalizer (L : Set (MulAut W))) :
    ∃ lam : ↥L, ∀ y : ↥L,
      (lam⁻¹ * y * lam ∈ (S : Subgroup ↥L)) ↔ (conjInvL t ht y ∈ (S : Subgroup ↥L)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let f : ↥L →* ↥L := (conjInvL t ht).symm.toMonoidHom
  have hf : Function.Surjective f := (conjInvL t ht).symm.surjective
  obtain ⟨lam, hlam⟩ := MulAction.exists_smul_eq ↥L S (Sylow.mapSurjective hf S)
  refine ⟨lam, fun y => ?_⟩
  have h1 : y ∈ ((lam • S : Sylow 2 ↥L) : Subgroup ↥L) ↔ lam⁻¹ * y * lam ∈ (S : Subgroup ↥L) := by
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp [MulAut.smul_def, mul_assoc]
  rw [hlam, Sylow.coe_mapSurjective, Subgroup.mem_map_equiv, MulEquiv.symm_symm] at h1
  exact h1.symm

private theorem map_adjust {V : Subgroup W} (hVinv : ∀ l ∈ L, ∀ v ∈ V, l v ∈ V) {t : MulAut W}
    (ht : t ∈ Subgroup.normalizer (L : Set (MulAut W))) (lam : ↥L) :
    V.map (((lam : MulAut W)⁻¹ * t : MulAut W)).toMonoidHom = V.map t.toMonoidHom := by
  have hlam : (lam : MulAut W) ∈ L := lam.2
  have hconj : ∀ l ∈ L, t⁻¹ * l * t ∈ L := by
    intro l hl
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ ht) l).mp hl
    simpa using this
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨(t⁻¹ * (lam : MulAut W)⁻¹ * t) v, hVinv _ (hconj _ (L.inv_mem hlam)) v hv, ?_⟩
    show (t * (t⁻¹ * (lam : MulAut W)⁻¹ * t)) v = ((lam : MulAut W)⁻¹ * t) v
    congr 1
    group
  · rintro ⟨v, hv, rfl⟩
    refine ⟨(t⁻¹ * (lam : MulAut W) * t) v, hVinv _ (hconj _ hlam) v hv, ?_⟩
    show ((lam : MulAut W)⁻¹ * t * (t⁻¹ * (lam : MulAut W) * t)) v = t v
    congr 1
    group

theorem typesFour_good_twist [Finite ↥L] {Q : Subgroup (MulAut W)} (S : Sylow 2 ↥L)
    (hS : ∀ b ∈ Subgroup.normalizer ((S : Subgroup ↥L) : Set ↥L), (b : MulAut W) ∈ Q)
    {t : MulAut W} (ht : t ∈ Subgroup.normalizer (L : Set (MulAut W))) {V : Subgroup W}
    (hsum : IsSumMod (fixV L) V (V.map t.toMonoidHom) ⊤)
    (h : (∃ n', 3 ≤ n' ∧ BinaryNaturalSL L V (V ⊓ fixV L) 3 n') ∨
      (∃ n', 3 ≤ n' ∧ BinaryNaturalSp4 L V (V ⊓ fixV L) n')) :
    ∃ a₀ ∈ Q, ∃ m : ℕ, Odd m ∧ a₀ ^ m = 1 ∧ ∀ w : W, a₀ w * w⁻¹ ∈ fixV L → w ∈ fixV L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have key : (∀ l ∈ L, ∀ v ∈ V, l v ∈ V) ∧ ∀ (S : Sylow 2 ↥L) (δ : ↥L ≃* ↥L),
      (∀ x, x ∈ (S : Subgroup ↥L) ↔ δ x ∈ (S : Subgroup ↥L)) →
      ∃ b ∈ Subgroup.normalizer ((S : Subgroup ↥L) : Set ↥L), ∃ m : ℕ, Odd m ∧ b ^ m = 1 ∧
        (∀ u ∈ V, ((b : MulAut W) u) * u⁻¹ ∈ V ⊓ fixV L → u ∈ V ⊓ fixV L) ∧
        (∀ u ∈ V, (((δ b : ↥L) : MulAut W) u) * u⁻¹ ∈ V ⊓ fixV L → u ∈ V ⊓ fixV L) := by
    rcases h with ⟨n', hn', K, _, _, hK, π, hπ⟩ | ⟨n', hn', K, _, _, hK, π, hπ⟩
    · have : CharP K 2 := by
        have := Fintype.ofFinite K
        exact charP_of_card_eq_prime_pow (f := n') (by rw [← Nat.card_eq_fintype_card, hK])
      refine ⟨fun l hl v hv => hπ.2.2.2.1 ⟨l, hl⟩ v hv, fun S δ hδ => ?_⟩
      exact natural_twist_element (StatedSL 3 K)
        (fun Q α hα => statedSL3_regular_twist hn' hK Q α hα) hπ S δ hδ
    · have : CharP K 2 := by
        have := Fintype.ofFinite K
        exact charP_of_card_eq_prime_pow (f := n') (by rw [← Nat.card_eq_fintype_card, hK])
      refine ⟨fun l hl v hv => hπ.2.2.2.1 ⟨l, hl⟩ v hv, fun S δ hδ => ?_⟩
      exact natural_twist_element (StatedSp 2 K)
        (fun Q α hα => statedSp4_regular_twist hn' hK Q α hα) hπ S δ hδ
  obtain ⟨hVinv, hex⟩ := key
  obtain ⟨lam, hlam⟩ := exists_adjust S ht
  set t' : MulAut W := ((lam : ↥L) : MulAut W)⁻¹ * t with ht'
  have ht'N : t' ∈ Subgroup.normalizer (L : Set (MulAut W)) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer lam.2)) ht
  have hδ : ∀ x : ↥L, x ∈ (S : Subgroup ↥L) ↔ conjInvL t' ht'N x ∈ (S : Subgroup ↥L) := by
    intro x
    have e1 : conjInvL t' ht'N x = conjInvL t ht (lam * x * lam⁻¹) := by
      apply Subtype.ext
      simp only [conjInvL_coe, ht', Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e1, ← hlam, show lam⁻¹ * (lam * x * lam⁻¹) * lam = x by group]
  obtain ⟨b, hbN, m, hm, hbm, hR1, hR2⟩ := hex S (conjInvL t' ht'N) hδ
  refine ⟨(b : MulAut W), hS b hbN, m, hm, by simpa using congrArg Subtype.val hbm, ?_⟩
  have hsum' : IsSumMod (fixV L) V (V.map t'.toMonoidHom) ⊤ := by
    rw [ht', map_adjust hVinv ht lam]
    exact hsum
  have hbA : ∀ a ∈ V, (b : MulAut W) a ∈ V := fun a ha => hVinv _ b.2 a ha
  have hconj' : ∀ l ∈ L, t'⁻¹ * l * t' ∈ L := by
    intro l hl
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ ht'N) l).mp hl
    simpa using this
  refine regular_of_sumMod hsum' hbA ?_ (fun c hc => hc _ b.2) ?_ ?_
  · rintro _ ⟨v, hv, rfl⟩
    refine ⟨(t'⁻¹ * (b : MulAut W) * t') v, hVinv _ (hconj' _ b.2) v hv, ?_⟩
    show (t' * (t'⁻¹ * (b : MulAut W) * t')) v = (b : MulAut W) (t' v)
    rw [show t' * (t'⁻¹ * (b : MulAut W) * t') = (b : MulAut W) * t' by group]
    rfl
  · intro a ha hw
    have := hR1 a ha ⟨(V.mul_mem (hbA a ha) (V.inv_mem ha)), hw⟩
    exact this.2
  · rintro _ ⟨v, hv, rfl⟩ hw
    have hw0 : (b : MulAut W) (t' v) * (t' v)⁻¹ ∈ fixV L := hw
    have hu : (t'⁻¹ * (b : MulAut W) * t') v ∈ V := hVinv _ (hconj' _ b.2) v hv
    have h3 : (b : MulAut W) (t' v) = t' ((t'⁻¹ * (b : MulAut W) * t') v) := by
      show ((b : MulAut W) * t') v = (t' * (t'⁻¹ * (b : MulAut W) * t')) v
      rw [show t' * (t'⁻¹ * (b : MulAut W) * t') = (b : MulAut W) * t' by group]
    have h2 : (b : MulAut W) (t' v) * (t' v)⁻¹ = t' ((t'⁻¹ * (b : MulAut W) * t') v * v⁻¹) := by
      rw [h3, map_mul, map_inv]
    have hw' : (t'⁻¹ * (b : MulAut W) * t') v * v⁻¹ ∈ fixV L := by
      have := fixV_of_normalizer (Subgroup.inv_mem _ ht'N) hw0
      rw [h2] at this
      simpa using this
    have hv' := hR2 v hv ⟨V.mul_mem hu (V.inv_mem hv), hw'⟩
    exact fixV_of_normalizer ht'N hv'.2

end Twist

end CFSG.Quasithin
