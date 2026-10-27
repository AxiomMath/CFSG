module

public import CFSG.Quasithin.MS93.S46Rec

public section

namespace CFSG.Quasithin.MS93.S45

open CFSG.Quasithin CFSG.Assembly.LowTwoRank Matrix
open scoped commutatorElement

variable {𝔾 : Type} [Group 𝔾] {F : Type} [Field F] [Fintype F] [CharP F 2] {n : ℕ}

theorem exists_dual_layer (h14 : MS14AS) (hSQ : SQTKQuot) (hsq : SQTKGroup (SL3 F))
    (hF : Fintype.card F = 2 ^ n) {K Q Z N T Y : Subgroup 𝔾} [Finite ↥K]
    {ψ : ↥K →* ↥(StatedSL 3 F)} (hψ : Function.Surjective ψ)
    (hQ : ∀ k : ↥K, toSL3 ψ k = 1 ↔ (k : 𝔾) ∈ Q) (hKZ : K ≤ Subgroup.normalizer (Z : Set 𝔾))
    (hKN : K ≤ Subgroup.normalizer (N : Set 𝔾)) (hZN : Z ≤ N) (hNK : N ≤ K)
    (hNN : ⁅N, N⁆ ≤ Z) (hNQ : ⁅N, Q⁆ ≤ Z) (hN2 : ∀ x ∈ N, x ^ 2 ∈ Z)
    (hQT : Q ≤ T) (hTK : T ≤ K)
    (hT : (T.subgroupOf K).map (toSL3 ψ) = rootGroup 1 0 ⊔ rootGroup 2 0)
    (hZY : Z ≤ Y) (hYK : Y ≤ K) (hYZ : Z.relIndex Y ≤ Fintype.card F) (hYT : ⁅Y, T⁆ ≤ Z)
    (hNTY : ⁅N, T⁆ ≤ Y) (hNTZ : ¬ ⁅N, T⁆ ≤ Z) :
    ∃ N₀ : Subgroup 𝔾, N₀ ≤ N ∧ ¬ N₀ ≤ Z ∧ IsSumOfNaturalModulesVia K N₀ Z ψ true 1 := by
  have : Finite ↥N := Finite.of_injective _ (Subgroup.inclusion_injective hNK)
  have : Finite ↥Y := Finite.of_injective _ (Subgroup.inclusion_injective hYK)
  have hNc : ∀ v ∈ N, ∀ w ∈ N, ⁅v, w⁆ ∈ Z := fun v hv w hw =>
    hNN (Subgroup.commutator_mem_commutator hv hw)
  have hker : ∀ l : ↥K, ψ l = 1 → ∀ v ∈ N, v⁻¹ * ((l : 𝔾) * v * (l : 𝔾)⁻¹) ∈ Z := by
    intro l hl v hv
    have hlQ : (l : 𝔾) ∈ Q := (hQ l).mp (by simp [toSL3, hl])
    have h1 := hNQ (Subgroup.commutator_mem_commutator (N.inv_mem hv) hlQ)
    rw [commutatorElement_def, inv_inv] at h1
    simpa [mul_assoc] using h1
  obtain ⟨X, _, π, ρ, hπs, hπk, hπρ⟩ := ML3.exists_quotient_action hψ hKN hZN hKZ hNc hker
  have : Finite X := Finite.of_surjective π hπs
  have hX2 : ∀ x : X, x ^ 2 = 1 := by
    intro x
    obtain ⟨v, rfl⟩ := hπs x
    rw [← map_pow]
    refine (hπk _).mpr ?_
    rw [Subgroup.coe_pow]
    exact hN2 v v.2
  have hπeq : ∀ v v' : ↥N, π v = π v' ↔ (v : 𝔾)⁻¹ * v' ∈ Z := fun v v' => by
    have := hπk (v⁻¹ * v')
    rw [map_mul, map_inv, inv_mul_eq_one] at this
    simpa using this
  set ρ' : SL3 F →* MulAut X := ρ.comp transposeInv with hρ'def
  have hρ' : ∀ g : SL3 F, ρ' (transposeInv g) = ρ g := fun g => by
    rw [hρ'def, MonoidHom.comp_apply, transposeInv_transposeInv]
  set ρK : ↥K →* MulAut X := ρ.comp (toSL3 ψ) with hρKdef
  have hρK : ∀ (k : ↥K) (v : ↥N), ρK k (π v) = π (conjOn hKN k v) := hπρ
  have hqPt : (qPt : Subgroup (SL3 F)).map ρ' = (T.subgroupOf K).map ρK := by
    rw [hρ'def, hρKdef, ← Subgroup.map_map, ← Subgroup.map_map, S46.map_transposeInv_qPt_eq, hT]
  set R := commV ((qPt : Subgroup (SL3 F)).map ρ') with hRdef
  have hpreR : S4A.F.pre π R = ⁅N, T⁆ ⊔ Z := by
    rw [hRdef, hqPt]
    exact S4A.F.pre_commV hρK hπk hZN hπs hTK
  have hcomm : Nat.card R ≤ Nat.card F := by
    rw [← S4A.F.card_pre hπk hZN hπs R, hpreR, Nat.card_eq_fintype_card]
    refine le_trans (Subgroup.relIndex_le_of_le_right (sup_le hNTY hZY) ?_) hYZ
    exact Subgroup.index_ne_zero_of_finite
  have hfixR : ∀ s ∈ (qPt : Subgroup (SL3 F)), ∀ r ∈ R, ρ' s r = r := by
    intro s hs r hr
    obtain ⟨v, rfl⟩ := hπs r
    have hvY : (v : 𝔾) ∈ Y := by
      have h1 : (v : 𝔾) ∈ S4A.F.pre π R := S4A.F.mem_pre.mpr ⟨v.2, hr⟩
      rw [hpreR] at h1
      exact sup_le hNTY hZY h1
    have hs' : transposeInv s ∈ (T.subgroupOf K).map (toSL3 ψ) := by
      rw [hT, ← S46.map_transposeInv_qPt_eq]
      exact ⟨s, hs, rfl⟩
    obtain ⟨t, htT, ht⟩ := hs'
    have e : ρ' s = ρ (toSL3 ψ t) := by rw [ht]; rfl
    rw [e, hπρ, eq_comm, hπeq]
    have h1 := hYT (Subgroup.commutator_mem_commutator (Y.inv_mem hvY)
      (Subgroup.mem_subgroupOf.mp htT))
    rw [commutatorElement_def, inv_inv] at h1
    simpa [coe_conjOn_apply, mul_assoc] using h1
  obtain ⟨n₁, hn₁, t₁, ht₁, hnt⟩ : ∃ n₁ ∈ N, ∃ t₁ ∈ T, ⁅n₁, t₁⁆ ∉ Z := by
    by_contra h
    push Not at h
    exact hNTZ (Subgroup.commutator_le.mpr h)
  set w := ⁅n₁, t₁⁆ with hwdef
  have hwN : w ∈ N := S4A.F.commutatorElement_mem_V hKN hn₁ (hTK ht₁)
  have hwR : π ⟨w, hwN⟩ ∈ R := by
    have h1 : w ∈ S4A.F.pre π R := by
      rw [hpreR]
      exact Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hn₁ ht₁)
    obtain ⟨_, h2⟩ := S4A.F.mem_pre.mp h1
    exact h2
  have hw1 : π ⟨w, hwN⟩ ≠ 1 := fun h => hnt ((hπk _).mp h)
  have hnt' : ∃ g x, ρ' g x ≠ x := by
    by_contra h
    push Not at h
    apply hw1
    have hle : R ≤ ⊥ := by
      rw [hRdef, commV, Subgroup.closure_le]
      rintro _ ⟨_, ⟨g, -, rfl⟩, x, rfl⟩
      rw [h g x, mul_inv_cancel]
      exact Subgroup.one_mem _
    exact Subgroup.mem_bot.mp (hle hwR)
  have hB : (qPt : Subgroup (SL3 F)) ≠ ⊥ := by
    intro h
    have h1 : rootElt 0 1 (1 : F) ∈ (qPt : Subgroup (SL3 F)) :=
      Subgroup.mem_sup_left (rootElt_mem_rootGroup 0 1 1)
    rw [h, Subgroup.mem_bot, rootElt_eq_one_iff (by decide)] at h1
    exact one_ne_zero h1
  have hB2 : ∀ b ∈ (qPt : Subgroup (SL3 F)), b ^ 2 = 1 := fun b hb => by
    rw [sq]
    exact ML3.qPt_elemAb.2 b hb
  have hqB : Nat.card F ≤ Nat.card (qPt : Subgroup (SL3 F)) := by
    rw [card_qPt]
    exact Nat.le_self_pow two_ne_zero _
  have hF' : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF]
  obtain ⟨hCP, -, -⟩ := S4A.F.dualOff_decomp h14 hSQ hsq hF' hX2 ρ' hnt' hB hB2
    ML3.qPt_elemAb.1 hqB hcomm
  set N₀ := Subgroup.closure {u | ∃ l : ↥K, (l : 𝔾) * w * (l : 𝔾)⁻¹ = u} ⊔ Z with hN₀def
  have hwN₀ : w ∈ N₀ := Subgroup.mem_sup_left (Subgroup.subset_closure ⟨1, by simp⟩)
  have hN₀N : N₀ ≤ N := by
    refine sup_le ?_ hZN
    rw [Subgroup.closure_le]
    rintro _ ⟨l, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hKN l.2) w).mp hwN
  have hKN₀ : K ≤ Subgroup.normalizer (N₀ : Set 𝔾) := by
    refine CFSG.LieType.Steinberg.le_normalizer_sup ?_ hKZ
    refine CFSG.LieType.Steinberg.le_normalizer_of_map_conj_le fun k hk => ?_
    rw [MonoidHom.map_closure]
    apply Subgroup.closure_mono
    rintro _ ⟨_, ⟨l, rfl⟩, rfl⟩
    exact ⟨⟨k, hk⟩ * l, by simp [mul_assoc]⟩
  have hwC : π ⟨w, hwN⟩ ∈ commV ρ'.range :=
    G6.commV_mono (Subgroup.map_le_range ρ' _) hwR
  have hN₀C : N₀ ≤ S4A.F.pre π (commV ρ'.range) := by
    refine sup_le ?_ (S4A.F.le_pre hπk hZN _)
    rw [Subgroup.closure_le]
    rintro _ ⟨l, rfl⟩
    have hlw : (l : 𝔾) * w * (l : 𝔾)⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.mp (hKN l.2) w).mp hwN
    refine S4A.F.mem_pre.mpr ⟨hlw, ?_⟩
    have e : π ⟨(l : 𝔾) * w * (l : 𝔾)⁻¹, hlw⟩ = ρ' (transposeInv (toSL3 ψ l)) (π ⟨w, hwN⟩) := by
      rw [hρ', hπρ]
      rfl
    rw [e]
    exact S46.commV_inv ρ' _ hwC
  have hmemT : ∀ l : ↥K, transposeInv (toSL3 ψ l) ∈ rootGroup 0 1 → (l : 𝔾) ∈ T := by
    intro l hl
    have h1 : toSL3 ψ l ∈ (T.subgroupOf K).map (toSL3 ψ) := by
      rw [hT, ← transposeInv_transposeInv (toSL3 ψ l)]
      refine Subgroup.mem_sup_left ?_
      rw [← M16.map_transposeInv_rootGroup]
      exact ⟨_, hl, rfl⟩
    obtain ⟨t, htT, ht⟩ := h1
    have h2 : (((t⁻¹ * l : ↥K)) : 𝔾) ∈ Q := (hQ _).mp (by rw [map_mul, map_inv, ht,
      inv_mul_cancel])
    have h3 : (l : 𝔾) = t * ((t⁻¹ * l : ↥K) : 𝔾) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
    rw [h3]
    exact T.mul_mem (Subgroup.mem_subgroupOf.mp htT) (hQT h2)
  refine ⟨N₀, hN₀N, fun h => hnt (h hwN₀), ?_⟩
  refine isSumOfNaturalModulesVia_dual_of_vecStab hψ hKN₀ le_sup_right hKZ
    (fun v hv w hw => hNc v (hN₀N hv) w (hN₀N hw)) (fun l hl v hv => hker l hl v (hN₀N hv))
    hwN₀ hnt ?_ ?_ ?_ rfl
  ·
    intro l hl
    have h1 := S46.ptLevi_fix_of_card ρ' hcomm hfixR hwR hl
    rw [hρ', hπρ, eq_comm, hπeq] at h1
    simpa [coe_conjOn_apply] using h1
  ·
    intro l l' hl hl' v hv
    have hlT := hmemT l hl
    have hl'T := hmemT l' hl'
    have hy : (l : 𝔾) * v * (l : 𝔾)⁻¹ * v⁻¹ ∈ Y := by
      have h1 : ⁅(l : 𝔾), v⁆ ∈ ⁅N, T⁆ := by
        rw [Subgroup.commutator_comm]
        exact Subgroup.commutator_mem_commutator hlT (hN₀N hv)
      rw [commutatorElement_def] at h1
      exact hNTY h1
    have h2 := hYT (Subgroup.commutator_mem_commutator (Y.inv_mem hy) hl'T)
    rw [commutatorElement_def, inv_inv] at h2
    simpa [mul_assoc] using h2
  ·
    intro v hv hfixv
    obtain ⟨hvN, hvC⟩ := S4A.F.mem_pre.mp (hN₀C hv)
    have hfix' : ∀ g ∈ (lnLevi : Subgroup (SL3 F)), ρ' g (π ⟨v, hvN⟩) = π ⟨v, hvN⟩ := by
      intro g hg
      obtain ⟨l, hl⟩ := toSL3_surjective hψ (transposeInv g)
      have h1 := hfixv l (by rw [hl, transposeInv_transposeInv]; exact hg)
      have e : ρ' g = ρ (toSL3 ψ l) := by rw [hl]; rfl
      rw [e, hπρ, eq_comm, hπeq]
      simpa [coe_conjOn_apply] using h1
    exact (hπk _).mp (S46.eq_one_of_lnLevi_fix ρ' hcomm hCP hvC hfix')

omit [CharP F 2] in
theorem le_relIndex_of_coord {K V Z Y₀ : Subgroup 𝔾} {ψ : ↥K →* ↥(StatedSL 3 F)} {dual : Bool}
    (hd : IsSumOfNaturalModulesVia K V Z ψ dual 1) (hYV : Y₀ ≤ V)
    {ι : Type} [Finite ι] (e : ι → Fin 3 → F) (he : Function.Injective e)
    (hmem : ∀ i, ∃ y ∈ Y₀, (NatSec.ofIsSum hd).coord y = e i) :
    Nat.card ι ≤ Z.relIndex Y₀ := by
  set Nn := NatSec.ofIsSum hd with hNn
  let f : ↥Y₀ →* Multiplicative (Fin 3 → F) :=
    { toFun := fun y => Multiplicative.ofAdd (Nn.coord y)
      map_one' := by simp [Nn.coord_one]
      map_mul' := fun y y' => by
        simp only [Subgroup.coe_mul]
        rw [Nn.coord_mul (hYV y.2) (hYV y'.2), ofAdd_add] }
  have hker : f.ker = Z.subgroupOf Y₀ := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show Multiplicative.ofAdd (Nn.coord y) = 1 ↔ _
    rw [← Nn.coord_eq_zero_iff (hYV y.2)]
    exact ⟨fun h1 => by simpa using h1, fun h1 => by rw [h1, ofAdd_zero]⟩
  have hrange : ∀ i, Multiplicative.ofAdd (e i) ∈ f.range := by
    intro i
    obtain ⟨y, hy, hye⟩ := hmem i
    exact ⟨⟨y, hy⟩, by show Multiplicative.ofAdd (Nn.coord y) = _; rw [hye]⟩
  let ι' : ι → ↥f.range := fun i => ⟨Multiplicative.ofAdd (e i), hrange i⟩
  have hι : Function.Injective ι' := fun i j hij => by
    have h1 : ((ι' i : ↥f.range) : Multiplicative (Fin 3 → F)) = ι' j := congrArg Subtype.val hij
    exact he (Multiplicative.ofAdd.injective h1)
  have hfin : Finite ↥f.range := Finite.of_injective (fun x => (x : Multiplicative (Fin 3 → F)))
    Subtype.val_injective
  rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]
  exact Nat.card_le_card_of_injective ι' hι

theorem isSum_dual_of_offender (h14 : MS14AS) (hSQ : SQTKQuot) (hsq : SQTKGroup (SL3 F))
    (hF : Fintype.card F = 2 ^ n) {K Q Z N T Y : Subgroup 𝔾} [Finite ↥K]
    {ψ : ↥K →* ↥(StatedSL 3 F)} (hψ : Function.Surjective ψ)
    (hQ : ∀ k : ↥K, toSL3 ψ k = 1 ↔ (k : 𝔾) ∈ Q) (hKZ : K ≤ Subgroup.normalizer (Z : Set 𝔾))
    (hKN : K ≤ Subgroup.normalizer (N : Set 𝔾)) (hZN : Z ≤ N) (hNK : N ≤ K)
    (hNN : ⁅N, N⁆ ≤ Z) (hNQ : ⁅N, Q⁆ ≤ Z) (hN2 : ∀ x ∈ N, x ^ 2 ∈ Z)
    (hQT : Q ≤ T) (hTK : T ≤ K)
    (hT : (T.subgroupOf K).map (toSL3 ψ) = rootGroup 1 0 ⊔ rootGroup 2 0)
    (hZY : Z ≤ Y) (hYK : Y ≤ K) (hYZ : Z.relIndex Y ≤ Fintype.card F) (hYT : ⁅Y, T⁆ ≤ Z)
    (hNTY : ⁅N, T⁆ ≤ Y) (hNTZ : ¬ ⁅N, T⁆ ≤ Z) (hgen : N ≤ conjCl K Y ⊔ Z) :
    IsSumOfNaturalModulesVia K N Z ψ true 1 := by
  obtain ⟨N₀, hN₀N, -, hd⟩ := exists_dual_layer h14 hSQ hsq hF hψ hQ hKZ hKN hZN hNK hNN hNQ
    hN2 hQT hTK hT hZY hYK hYZ hYT hNTY hNTZ
  have : Finite ↥Y := Finite.of_injective _ (Subgroup.inclusion_injective hYK)
  set Nn := NatSec.ofIsSum hd with hNn
  have hKN₀ := hd.1
  have hZN₀ : Z ≤ N₀ := hd.2.1
  set Y₀ := ⁅N₀, T⁆ ⊔ Z with hY₀
  have hTN₀ : T ≤ Subgroup.normalizer (N₀ : Set 𝔾) := hTK.trans hKN₀
  have hY₀N₀ : Y₀ ≤ N₀ :=
    sup_le (Subgroup.le_normalizer_iff_commutator_le_left.mp hTN₀) hZN₀
  have hY₀Y : Y₀ ≤ Y := sup_le ((Subgroup.commutator_mono hN₀N le_rfl).trans hNTY) hZY
  have : Finite ↥Y₀ := Finite.of_injective _ (Subgroup.inclusion_injective hY₀Y)
  obtain ⟨v₁, hv₁, hv₁c⟩ := Nn.exists_coord_eq (Pi.single 1 1)
  have hreal : ∀ c : F, ∃ y ∈ Y₀, Nn.coord y = Pi.single 0 (-c) := by
    intro c
    have hc : rootElt 1 0 c ∈ (T.subgroupOf K).map (toSL3 ψ) := by
      rw [hT]
      exact Subgroup.mem_sup_left (rootElt_mem_rootGroup 1 0 c)
    obtain ⟨t, htT, ht⟩ := hc
    have htT' : (t : 𝔾) ∈ T := Subgroup.mem_subgroupOf.mp htT
    have hconj := Nn.conj_mem t hv₁
    refine ⟨(t : 𝔾) * v₁ * (t : 𝔾)⁻¹ * v₁⁻¹, ?_, ?_⟩
    · refine Subgroup.mem_sup_left ?_
      have h1 : ⁅(t : 𝔾), v₁⁆ ∈ ⁅T, N₀⁆ := Subgroup.commutator_mem_commutator htT' hv₁
      rw [Subgroup.commutator_comm, commutatorElement_def] at h1
      exact h1
    · rw [Nn.coord_mul hconj (N₀.inv_mem hv₁), Nn.coord_inv hv₁, Nn.coord_conj t hv₁,
        natAct_true, ht, hv₁c, dualMat_rootElt_mulVec (by decide)]
      simp
  have hq : Fintype.card F ≤ Z.relIndex Y₀ := by
    rw [← Nat.card_eq_fintype_card]
    refine le_relIndex_of_coord hd hY₀N₀ (fun c : F => Pi.single 0 (-c))
      (fun c c' hcc => ?_) hreal
    have := congrFun hcc 0
    simpa using this
  have hYY₀ : Y ≤ Y₀ := by
    have hmul := Subgroup.relIndex_mul_relIndex Z Y₀ Y le_sup_right hY₀Y
    have hpos : 0 < Z.relIndex Y₀ := Nat.pos_of_ne_zero (by
      rw [Subgroup.relIndex]; exact Subgroup.index_ne_zero_of_finite)
    have h1 : Y₀.relIndex Y = 1 := by
      have h2 : Z.relIndex Y₀ * Y₀.relIndex Y ≤ Z.relIndex Y₀ * 1 := by
        rw [hmul, mul_one]; exact hYZ.trans hq
      have h3 := Nat.le_of_mul_le_mul_left h2 hpos
      have h4 : Y₀.relIndex Y ≠ 0 := by
        rw [Subgroup.relIndex]; exact Subgroup.index_ne_zero_of_finite
      omega
    exact Subgroup.relIndex_eq_one.mp h1
  have hYN₀ : Y ≤ N₀ := hYY₀.trans hY₀N₀
  have hNN₀ : N ≤ N₀ := hgen.trans (sup_le (iSup₂_le fun k hk =>
    (Subgroup.map_mono hYN₀).trans (map_conj_eq_of_mem_normalizer (hKN₀ hk)).le) hZN₀)
  have hNeq : N = N₀ := le_antisymm hNN₀ hN₀N
  rw [hNeq]
  exact hd

end CFSG.Quasithin.MS93.S45
