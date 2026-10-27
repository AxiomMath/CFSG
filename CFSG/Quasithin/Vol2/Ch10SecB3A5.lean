module

public import CFSG.Quasithin.Vol2.Ch10SecB3L32

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin CFSG.QuasithinUnique

theorem eq_top_of_card_sixty {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    (hQ : Nat.card Q = 60) {X : Subgroup Q} (h4 : 4 ∣ Nat.card X) (h5 : 5 ∣ Nat.card X) :
    X = ⊤ := by
  have hX : Nat.card X * X.index = 60 := hQ ▸ X.card_mul_index
  have h20 : 20 ∣ Nat.card X := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h4 h5
  obtain ⟨k, hk⟩ := h20
  have hk' : k * X.index = 3 := by
    have : 20 * (k * X.index) = 20 * 3 := by rw [← mul_assoc, ← hk, hX]
    omega
  rcases (Nat.dvd_prime Nat.prime_three).mp (Dvd.intro_left _ hk') with h | h
  · exact Subgroup.index_eq_one.mp h
  · exfalso
    have hcore := Subgroup.index_normalCore_le_factorial_index (H := X)
    rw [h] at hcore
    rcases (X.normalCore_normal).eq_bot_or_eq_top with hb | ht
    · rw [hb, Subgroup.index_bot, hQ] at hcore
      norm_num at hcore
    · have : X = ⊤ := top_le_iff.mp (ht ▸ X.normalCore_le)
      rw [this, Subgroup.index_top] at h
      omega

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

@[expose] noncomputable def autCoordQ {Q : Type*} [Group Q] (ψ : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* Q)
    {s : G} (hs : s ∈ Subgroup.normalizer (L : Set G)) : MulAut Q :=
  ψ.symm.trans ((autQuot2 ↥L (conjAct L ⟨s, hs⟩)).trans ψ)

omit [Finite G] in
theorem autCoordQ_apply {Q : Type*} [Group Q] (ψ : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* Q) {s : G}
    (hs : s ∈ Subgroup.normalizer (L : Set G)) {x : G} (hx : x ∈ L) (hx' : s * x * s⁻¹ ∈ L) :
    ψ (mkO2 L (s * x * s⁻¹) hx') = autCoordQ ψ hs (ψ (mkO2 L x hx)) := by
  simp only [autCoordQ, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rw [mkO2, mkO2, autQuot2_mk]
  congr 2

theorem exists_coordQ
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hyp : Hyp10 G T L I) {Q : Type} [Group Q] (e : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* Q) {t : G}
    (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G)) :
    ∃ (Ψ : ↥(fsuL0 T L) →* Q × Q) (α : MulAut Q), Function.Surjective Ψ ∧
      (∀ y : ↥(fsuL0 T L), Ψ y = 1 ↔ (y : G) ∈ pCoreOf 2 (fsuL0 T L)) ∧
      (∀ (l : G) (hl0 : l ∈ fsuL0 T L) (hl : l ∈ L), Ψ ⟨l, hl0⟩ = (e (mkO2 L l hl), 1)) ∧
      ∀ (y : ↥(fsuL0 T L)) (hy : t⁻¹ * y * t ∈ fsuL0 T L),
        Ψ ⟨t⁻¹ * y * t, hy⟩ = (α (Ψ y).2, (Ψ y).1) := by
  obtain ⟨φ, hφs, hφk, hφL, hφLt⟩ := SecA.exists_fsuL0_prod h37 h38 hyp ht htn
  let θ := quotO2Equiv (conjEquiv L t)
  let ψ2 := θ.symm.trans e
  let Ψ : ↥(fsuL0 T L) →* Q × Q := (e.toMonoidHom.prodMap ψ2.toMonoidHom).comp φ
  have hΨ : ∀ y, Ψ y = (e (φ y).1, ψ2 (φ y).2) := fun _ => rfl
  have hΨL : ∀ (l : G) (hl : l ∈ L), Ψ ⟨l, SecA.le_fsuL0 T L hl⟩ = (e (mkO2 L l hl), 1) := by
    intro l hl
    rw [hΨ, hφL l hl]
    simp [ψ2]
  have hΨLt : ∀ (l : G) (hl : l ∈ L) (hl' : t⁻¹ * l * t ∈ fsuL0 T L),
      Ψ ⟨t⁻¹ * l * t, hl'⟩ = (1, e (mkO2 L l hl)) := by
    intro l hl hl'
    have hm := conj_mem_conjugate' t hl
    have h1 := hφLt _ hm
    rw [hΨ, show (⟨t⁻¹ * l * t, hl'⟩ : ↥(fsuL0 T L)) =
      ⟨t⁻¹ * l * t, SecA.conjugate_le_fsuL0 ht hm⟩ from rfl, h1]
    refine Prod.ext (by simp) ?_
    show e (θ.symm (mkO2 (CFSG.conjugate L t) _ hm)) = e (mkO2 L l hl)
    rw [← quotO2Equiv_conjEquiv_mk t hl hm, MulEquiv.symm_apply_apply]
  have hΨc : ∀ (y z : ↥(fsuL0 T L)), (y : G) = z → Ψ y = Ψ z := fun y z h =>
    congrArg Ψ (Subtype.ext h)
  clear_value Ψ
  have hL0eq := SecA.fsuL0_eq_sup h37 h38 hyp ht htn
  have hLle : L ≤ fsuL0 T L := SecA.le_fsuL0 T L
  have hLtle : CFSG.conjugate L t ≤ fsuL0 T L := fun x hx => SecA.conjugate_le_fsuL0 ht hx
  have ht2 : t⁻¹ * t⁻¹ ∈ Subgroup.normalizer (L : Set G) := by
    have := Subgroup.inv_mem _ (SecA.mul_self_mem_normalizer h37 h38 hyp ht htn)
    simpa [mul_inv_rev] using this
  have hLt_iff : ∀ {x : G}, x ∈ CFSG.conjugate L t ↔ t * x * t⁻¹ ∈ L := SecA.mem_conjugate_iff
  let α : MulAut Q := autCoordQ e ht2
  let σ : Q × Q →* Q × Q := (α.toMonoidHom.comp (MonoidHom.snd _ _)).prod (MonoidHom.fst _ _)
  refine ⟨Ψ, α, fun p => ?_, fun y => ?_, fun l hl0 hl => ?_, ?_⟩
  · obtain ⟨y, hy⟩ := hφs (e.symm p.1, ψ2.symm p.2)
    exact ⟨y, by rw [hΨ, hy]; simp⟩
  · rw [hΨ, Prod.mk_eq_one, MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff, ← Prod.mk_eq_one,
      Prod.mk.eta, ← MonoidHom.mem_ker, hφk, Subgroup.mem_subgroupOf]
  · rw [hΨc ⟨l, hl0⟩ ⟨l, hLle hl⟩ rfl, hΨL l hl]
  · have htN : t⁻¹ ∈ Subgroup.normalizer (fsuL0 T L : Set G) :=
      Subgroup.inv_mem _ (SecA.le_fsuM T L ht)
    have hfg : Ψ.comp (conjHom (fsuL0 T L) htN) = σ.comp Ψ := by
      refine hom_ext_of_sup hLle hLtle hL0eq.symm (fun l hl => ?_) (fun l hl => ?_)
      · have hm : t⁻¹ * l * t ∈ fsuL0 T L := hLtle (conj_mem_conjugate' t hl)
        rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hΨL l hl,
          hΨc _ ⟨t⁻¹ * l * t, hm⟩ (by rw [conjHom_coe, inv_inv]), hΨLt l hl hm]
        simp [σ]
      · have hl' := hLt_iff.mp hl
        have hm2 : t⁻¹ * t⁻¹ * (t * l * t⁻¹) * (t⁻¹ * t⁻¹)⁻¹ ∈ L :=
          (Subgroup.mem_normalizer_iff.mp ht2 _).mp hl'
        have hm : t⁻¹ * (t * l * t⁻¹) * t ∈ fsuL0 T L := by simpa [mul_assoc] using hLtle hl
        rw [MonoidHom.comp_apply, MonoidHom.comp_apply,
          hΨc _ ⟨_, hLle hm2⟩ (by rw [conjHom_coe]; group), hΨL _ hm2,
          autCoordQ_apply e ht2 hl' hm2,
          hΨc ⟨l, hLtle hl⟩ ⟨_, hm⟩ (by group), hΨLt _ hl' hm]
        rfl
    intro y hy
    have h := congrArg (fun f => f y) hfg
    simp only [MonoidHom.comp_apply] at h
    rw [show (⟨t⁻¹ * y * t, hy⟩ : ↥(fsuL0 T L)) = conjHom (fsuL0 T L) htN y from
      Subtype.ext (by rw [conjHom_coe, inv_inv]), h]
    rfl

theorem card_alt5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  rfl

theorem card_D1_of_A5 (hyp : Hyp10 G T L I)
    (hcard : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 60) : Nat.card (D1 T L) = 4 := by
  obtain ⟨-, hp, hodd⟩ := isSylowTwoOf_D1 hyp
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
  have h1 := Subgroup.relIndex_mul_card (D1 T L) ⊤
  rw [inf_top_eq, Subgroup.card_top, hcard, hk] at h1
  have hodd' : ¬ 2 ∣ (D1 T L).relIndex ⊤ := hodd
  have hk5 : k ≤ 5 := by
    by_contra h
    have : 2 ^ 6 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h0 : 0 < (D1 T L).relIndex ⊤ := Nat.pos_of_ne_zero (by rintro h'; rw [h'] at h1; omega)
    have := Nat.le_mul_of_pos_left (2 ^ k) h0
    omega
  rw [hk]
  interval_cases k <;> omega

theorem not_four_of_A5 (h331 : Stmt3_3_1) (hyp : Hyp10 G T L I)
    (e : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* alternatingGroup (Fin 5)) {H : Subgroup G}
    (hH : IsHStar T (fsuM T L) H) {b₀ : G} (hb0 : b₀ ∈ fsuL0 T L)
    (hbX : b₀ ∈ H ⊓ fsuM T L) (ho : orderOf b₀ = 2 ^ 4 - 1) {t : G} (ht : t ∈ T)
    {Ψ : ↥(fsuL0 T L) →* alternatingGroup (Fin 5) × alternatingGroup (Fin 5)}
    {α : MulAut (alternatingGroup (Fin 5))}
    (hΨk : ∀ y : ↥(fsuL0 T L), Ψ y = 1 ↔ (y : G) ∈ pCoreOf 2 (fsuL0 T L))
    (hΨL : ∀ (l : G) (hl0 : l ∈ fsuL0 T L) (hl : l ∈ L), Ψ ⟨l, hl0⟩ = (e (mkO2 L l hl), 1))
    (hΨt : ∀ (y : ↥(fsuL0 T L)) (hy : t⁻¹ * y * t ∈ fsuL0 T L),
      Ψ ⟨t⁻¹ * y * t, hy⟩ = (α (Ψ y).2, (Ψ y).1))
    (hcardL : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 60) : False := by
  have hO : IsPGroup 2 (pCoreOf 2 (fsuL0 T L)) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  set Y := (H ⊓ fsuM T L) ⊓ fsuL0 T L with hYdef
  have hTX : T ≤ H ⊓ fsuM T L := le_inf hH.1.1 (SecA.le_fsuM T L)
  have htX := hTX ht
  have hz₀o : orderOf (b₀ ^ 3) = 5 := by
    rw [orderOf_pow_of_dvd (by norm_num) (by rw [ho]; norm_num), ho]
    norm_num
  have hz₀0 : b₀ ^ 3 ∈ fsuL0 T L := Subgroup.pow_mem _ hb0 3
  have hz₀Y : b₀ ^ 3 ∈ Y := Subgroup.pow_mem _ (show b₀ ∈ Y from ⟨hbX, hb0⟩) 3
  have hΨz₀ : Ψ ⟨b₀ ^ 3, hz₀0⟩ ≠ 1 := by
    intro h
    have h1 : b₀ ^ 3 = 1 := eq_one_of_mem_of_odd hO ((hΨk _).mp h) (by rw [hz₀o]; decide)
    rw [h1, orderOf_one] at hz₀o
    omega
  have hΨz₀5 : (Ψ ⟨b₀ ^ 3, hz₀0⟩) ^ 5 = 1 := by
    rw [← map_pow]
    have : (⟨b₀ ^ 3, hz₀0⟩ : ↥(fsuL0 T L)) ^ 5 = 1 :=
      Subtype.ext (by simp [← hz₀o])
    rw [this, map_one]
  obtain ⟨z, hz0, hzY, hz1, hz5⟩ : ∃ (z : G) (hz0 : z ∈ fsuL0 T L), z ∈ Y ∧
      (Ψ ⟨z, hz0⟩).1 ≠ 1 ∧ (Ψ ⟨z, hz0⟩).1 ^ 5 = 1 := by
    by_cases hx : (Ψ ⟨b₀ ^ 3, hz₀0⟩).1 = 1
    · have hy : (Ψ ⟨b₀ ^ 3, hz₀0⟩).2 ≠ 1 := fun hy => hΨz₀ (Prod.ext hx hy)
      have htM := SecA.le_fsuM T L ht
      have hm : t * b₀ ^ 3 * t⁻¹ ∈ fsuL0 T L := (Subgroup.mem_normalizer_iff.mp htM _).mp hz₀0
      have hm' : t⁻¹ * (t * b₀ ^ 3 * t⁻¹) * t ∈ fsuL0 T L := by simpa [mul_assoc] using hz₀0
      have hsw := hΨt ⟨t * b₀ ^ 3 * t⁻¹, hm⟩ hm'
      have e1 : (⟨t⁻¹ * (t * b₀ ^ 3 * t⁻¹) * t, hm'⟩ : ↥(fsuL0 T L)) = ⟨b₀ ^ 3, hz₀0⟩ :=
        Subtype.ext (by group)
      rw [e1] at hsw
      have hfst : (Ψ ⟨t * b₀ ^ 3 * t⁻¹, hm⟩).1 = (Ψ ⟨b₀ ^ 3, hz₀0⟩).2 := by rw [hsw]
      refine ⟨_, hm, ⟨(H ⊓ fsuM T L).mul_mem ((H ⊓ fsuM T L).mul_mem htX hz₀Y.1)
        ((H ⊓ fsuM T L).inv_mem htX), hm⟩, hfst ▸ hy, ?_⟩
      rw [hfst, ← Prod.pow_snd, hΨz₀5, Prod.snd_one]
    · exact ⟨_, hz₀0, hz₀Y, hx, by rw [← Prod.pow_fst, hΨz₀5, Prod.fst_one]⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hz1o : orderOf (Ψ ⟨z, hz0⟩).1 = 5 := orderOf_eq_prime hz5 hz1
  set A₁ : Subgroup (alternatingGroup (Fin 5)) := (imgIn Ψ Y).map (MonoidHom.fst _ _)
  have hzA : (Ψ ⟨z, hz0⟩).1 ∈ A₁ := ⟨_, mem_imgIn.mpr ⟨z, hz0, hzY, rfl⟩, rfl⟩
  have h5 : 5 ∣ Nat.card A₁ := by
    have := Subgroup.orderOf_dvd_natCard A₁ hzA
    rwa [hz1o] at this
  have hD : ∀ d ∈ T ⊓ L, ∀ hdL : d ∈ L,
      (e (mkO2 L d hdL), (1 : alternatingGroup (Fin 5))) ∈ imgIn Ψ Y := fun d hd hdL =>
    mem_imgIn.mpr ⟨d, SecA.le_fsuL0 T L hdL, ⟨hTX hd.1, SecA.le_fsuL0 T L hdL⟩, hΨL d _ hdL⟩
  have hDA : (D1 T L).map e.toMonoidHom ≤ A₁ := by
    rintro _ ⟨_, ⟨⟨d, hdL⟩, hdT, rfl⟩, rfl⟩
    exact ⟨_, hD d (Subgroup.mem_subgroupOf.mp hdT) hdL, rfl⟩
  have h4 : 4 ∣ Nat.card A₁ := by
    have := Subgroup.card_dvd_of_le hDA
    rwa [Subgroup.card_map_of_injective e.injective, card_D1_of_A5 hyp hcardL] at this
  have hA₁ : A₁ = ⊤ := eq_top_of_card_sixty card_alt5 h4 h5
  set N₁ : Subgroup (alternatingGroup (Fin 5)) := (imgIn Ψ Y).comap (MonoidHom.inl _ _)
  have hN₁ : N₁.Normal := ⟨fun x hx g => by
    have hg : g ∈ A₁ := hA₁ ▸ Subgroup.mem_top g
    obtain ⟨p, hp, rfl⟩ := hg
    have h := (imgIn Ψ Y).mul_mem ((imgIn Ψ Y).mul_mem hp hx) ((imgIn Ψ Y).inv_mem hp)
    have heq : p * (x, 1) * p⁻¹ = (p.1 * x * p.1⁻¹, 1) := by ext <;> simp
    show (p.1 * x * p.1⁻¹, (1 : alternatingGroup (Fin 5))) ∈ imgIn Ψ Y
    rw [← heq]
    exact h⟩
  have hN₁ne : N₁ ≠ ⊥ := by
    have hD1 : D1 T L ≠ ⊥ := fun h => by
      have := card_D1_of_A5 hyp hcardL
      rw [h, Subgroup.card_bot] at this
      omega
    obtain ⟨⟨q, hq⟩, hq1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hD1
    obtain ⟨⟨d, hdL⟩, hdT, rfl⟩ := hq
    intro hb
    have hmem : e (mkO2 L d hdL) ∈ N₁ := hD d (Subgroup.mem_subgroupOf.mp hdT) hdL
    rw [hb, Subgroup.mem_bot, MulEquiv.map_eq_one_iff] at hmem
    exact hq1 (Subtype.ext hmem)
  have hN₁top : N₁ = ⊤ := hN₁.eq_bot_or_eq_top.resolve_left hN₁ne
  apply not_le_of_isHStar h331 hyp hH
  intro l hl
  have hl0 := SecA.le_fsuL0 T L hl
  have hm : (e (mkO2 L l hl), (1 : alternatingGroup (Fin 5))) ∈ imgIn Ψ Y :=
    (show e (mkO2 L l hl) ∈ N₁ from hN₁top ▸ Subgroup.mem_top _)
  obtain ⟨y, hy0, hyY, hΨy⟩ := mem_imgIn.mp hm
  have hk0 : l * y⁻¹ ∈ fsuL0 T L := (fsuL0 T L).mul_mem hl0 ((fsuL0 T L).inv_mem hy0)
  have hk : l * y⁻¹ ∈ pCoreOf 2 (fsuL0 T L) := by
    apply (hΨk ⟨l * y⁻¹, hk0⟩).mp
    have e1 : (⟨l * y⁻¹, hk0⟩ : ↥(fsuL0 T L)) = ⟨l, hl0⟩ * ⟨y, hy0⟩⁻¹ := rfl
    rw [e1, map_mul, map_inv, hΨy, hΨL l hl0 hl, mul_inv_cancel]
  have hkY : l * y⁻¹ ∈ Y := ⟨hTX (SecA.pCoreOf_fsuL0_le_T0 hyp.fsu.sylow hk).1, hk0⟩
  have := Y.mul_mem hkY hyY
  simpa using this.1.1

theorem eq_two_of_A5
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h322 : TmpL6_3_2_2_two) (h331 : Stmt3_3_1) (h1013 : Stmt10_1_3) (hyp : Hyp10 G T L I)
    (e : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* alternatingGroup (Fin 5)) {H : Subgroup G}
    (hH : IsHStar T (fsuM T L) H) (hfaith : HallFaithful T L I H) {B : Subgroup G}
    (hB : QuasithinUnique.Lin2.IsHallTwoPrimeOf B (H ⊓ fsuM T L)) {n : ℕ} (hn2 : 2 ≤ n)
    {b₀ : G} (hb₀ : b₀ ∈ B) (ho : orderOf b₀ = 2 ^ n - 1) : n = 2 := by
  have hcardL : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 60 := by
    rw [Nat.card_congr e.toEquiv, card_alt5]
  have hodd : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ Nat.card (MulAut (↥L ⧸ CFSG.pCore 2 ↥L)) →
      r ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) := by
    intro r hr hr2 hd
    rw [card_mulAut_of_equiv_A5 e, show (120 : ℕ) = 2 * 60 by norm_num] at hd
    rw [hcardL]
    rcases (Nat.Prime.dvd_mul hr).mp hd with h | h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h) hr2
    · exact h
  have hbX := hB.1 hb₀
  have hbodd : Odd (orderOf b₀) := hB.2.1.of_dvd_nat (B.orderOf_dvd_natCard hb₀)
  have hb0 : b₀ ∈ fsuL0 T L := mem_fsuL0_of_odd h37 h38 h322 h1013 hyp hfaith hB hodd hbX hbodd
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp hyp.not_normal
  obtain ⟨Ψ, α, hΨs, hΨk, hΨL, hΨt⟩ := exists_coordQ h37 h38 hyp e ht htn
  have hO : IsPGroup 2 (pCoreOf 2 (fsuL0 T L)) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hp60 : ∀ p : alternatingGroup (Fin 5) × alternatingGroup (Fin 5), p ^ 60 = 1 := by
    intro p
    have h1 := pow_card_eq_one' (G := alternatingGroup (Fin 5)) (x := p.1)
    have h2 := pow_card_eq_one' (G := alternatingGroup (Fin 5)) (x := p.2)
    rw [card_alt5] at h1 h2
    exact Prod.ext h1 h2
  have h60 : b₀ ^ 60 = 1 := by
    have h1 := hp60 (Ψ ⟨b₀, hb0⟩)
    rw [← map_pow, hΨk] at h1
    exact eq_one_of_mem_of_odd hO (by simpa using h1)
      (hbodd.of_dvd_nat (orderOf_pow_dvd 60))
  have hd : 2 ^ n - 1 ∣ 60 := ho ▸ orderOf_dvd_of_pow_eq_one h60
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  have hn5 : n ≤ 5 := by
    by_contra h
    have : 2 ^ 6 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    have := Nat.le_of_dvd (by norm_num) hd
    omega
  interval_cases n
  · rfl
  · norm_num at hd
  · exfalso
    exact not_four_of_A5 h331 hyp e hH hb0 hbX ho ht hΨk hΨL hΨt hcardL
  · norm_num at hd

end CFSG.Quasithin.Vol2.Ch10.SecB
