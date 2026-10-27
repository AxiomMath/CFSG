module

public import CFSG.Quasithin.Vol2.Ch10SecAShape
public import CFSG.LieType.Ree.SuzukiSimple
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppEPerm
public import CFSG.Quasithin.Background.B2FactorizationResidual
public import CFSG.Quasithin.Vol2.Ch10SecBCoordL0
public import CFSG.Quasithin.Vol2.Ch10SecBPre
public import CFSG.Quasithin.Vol2.Ch10StatementsB

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin CFSG.QuasithinUnique

abbrev BenderHyp (K : Type) [Group K] : Prop :=
  (∃ (F : Type) (_ : Field F) (_ : Finite F) (a : ℕ), 2 ≤ a ∧ Nat.card F = 2 ^ a ∧
      Nonempty (K ≃* Matrix.SpecialLinearGroup (Fin 2) F)) ∨
    ∃ n : ℕ, CFSG.Blueprint.SuzukiModel K 2 n

theorem simple_even_of_bender
    {K : Type} [Group K] (h : BenderHyp K) :
    IsSimpleGroup K ∧ 2 ∣ Nat.card K := by
  rcases h with ⟨F, _, _, a, ha, hF, ⟨e⟩⟩ | ⟨n, -, b, hb, F, _, _, rfl, hF, ⟨e⟩⟩
  · have : Fintype F := Fintype.ofFinite F
    have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) F) :=
      CFSG.QuasithinUnique.AppE.sl2_isSimpleGroup ha (by rw [← Nat.card_eq_fintype_card]; exact hF)
    refine ⟨e.isSimpleGroup, ?_⟩
    rw [Nat.card_congr e.toEquiv, SecA.card_SL_two_pow hF]
    exact Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
  · obtain ⟨-, -, hs⟩ := CFSG.LieType.Ree.suzuki_simple hb hF
    refine ⟨e.isSimpleGroup, ?_⟩
    rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hF]
    exact Dvd.dvd.mul_right
      (Dvd.dvd.mul_right (dvd_pow (dvd_pow_self 2 (by omega)) two_ne_zero) _) _

variable {G : Type} [Group G]

theorem not_L32_of_SL2 {L : Subgroup G} {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 < n)
    (hK : Nat.card K = 2 ^ n)
    (e : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* Matrix.SpecialLinearGroup (Fin 2) K) : ¬ LBarL32 L := by
  rintro ⟨e'⟩
  have h1 := (Nat.card_congr e.toEquiv).symm.trans (Nat.card_congr e'.toEquiv)
  rw [SecA.card_SL_two_pow hK, SecA.card_SL_three_zmod_two] at h1
  have h2 : 2 ^ n * (4 ^ n - 1) = 2 ^ 3 * 21 := h1.trans (by norm_num)
  have hodd : Odd (4 ^ n - 1) := Nat.Even.sub_odd (Nat.one_le_pow _ _ (by norm_num))
    (Nat.even_pow.mpr ⟨by decide, by omega⟩) odd_one
  obtain ⟨h3, h4⟩ := SecA.two_pow_mul_odd_inj hodd (by decide) h2
  subst h3
  norm_num at h4

theorem not_L32_of_suzuki
    {L : Subgroup G} {n : ℕ}
    (hsz : CFSG.Blueprint.SuzukiModel (↥L ⧸ CFSG.pCore 2 ↥L) 2 n) : ¬ LBarL32 L := by
  rintro ⟨e'⟩
  obtain ⟨-, a, -, K, _, _, rfl, hK, ⟨e⟩⟩ := hsz
  have hc := (Nat.card_congr e.toEquiv).symm.trans (Nat.card_congr e'.toEquiv)
  rw [CFSG.LieType.Ree.suzuki_order hK, SecA.card_SL_three_zmod_two] at hc
  exact SecA.three_not_dvd_card_suzuki a (hc ▸ (by norm_num : 3 ∣ 168))

theorem bender_of_cases
    {T L I : Subgroup G}
    (hc : (∃ n, Case10_1_1One T L I n) ∨ (∃ n, Case10_1_1Four T L I n) ∨ Case10_1_1Seven T L I) :
    BenderHyp (↥L ⧸ CFSG.pCore 2 ↥L) ∧ ¬ LBarL32 L := by
  rcases hc with ⟨n, hn, ⟨K, _, _, hK, ⟨e⟩⟩, -⟩ | ⟨n, hn, ⟨K, _, _, hK, ⟨e⟩⟩, -⟩ | ⟨n, hsz, -⟩
  · exact ⟨Or.inl ⟨K, inferInstance, inferInstance, n, by omega, hK, ⟨e⟩⟩,
      not_L32_of_SL2 hn hK e⟩
  · exact ⟨Or.inl ⟨K, inferInstance, inferInstance, 2 * n, by omega, hK, ⟨e⟩⟩,
      not_L32_of_SL2 (by omega) hK e⟩
  · exact ⟨Or.inr ⟨n, hsz⟩, not_L32_of_suzuki hsz⟩

theorem eq_of_le_isPGroup {Q : Type*} [Group Q] [Finite Q] {P R : Subgroup Q}
    (hP : ¬ 2 ∣ P.index) (hR : IsPGroup 2 R) (hPR : P ≤ R) : R = P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hR
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (hk ▸ Subgroup.relIndex_dvd_card P R)
  have h1 := Subgroup.relIndex_dvd_index_of_le hPR
  rw [hj] at h1
  have hj0 : j = 0 := by
    by_contra h
    exact hP ((dvd_pow_self 2 h).trans h1)
  rw [hj0, pow_zero, Subgroup.relIndex_eq_one] at hj
  exact le_antisymm hj hPR

theorem mem_normalizer_of_map_eq {Q : Type*} [Group Q] {D : Subgroup Q} {α : MulAut Q}
    (hα : D.map α.toMonoidHom = D) {b : Q} (hb : α b ∈ Subgroup.normalizer (D : Set Q)) :
    b ∈ Subgroup.normalizer (D : Set Q) := by
  have key : ∀ x, x ∈ D ↔ α x ∈ D := by
    intro x
    constructor
    · intro hx
      rw [← hα]
      exact ⟨x, hx, rfl⟩
    · intro hx
      rw [← hα] at hx
      obtain ⟨x', hx', he⟩ := hx
      rwa [← α.injective he]
  refine Subgroup.mem_normalizer_iff.mpr fun d => ?_
  rw [key d, key (b * d * b⁻¹), map_mul, map_mul, map_inv]
  exact Subgroup.mem_normalizer_iff.mp hb (α d)

variable [Finite G] {T L I : Subgroup G}

theorem D1_ne_bot (hyp : Hyp10 G T L I) (h2 : 2 ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L)) :
    D1 T L ≠ ⊥ := by
  intro h
  obtain ⟨-, -, hodd⟩ := isSylowTwoOf_D1 hyp
  rw [h, Subgroup.bot_subgroupOf, Subgroup.index_bot, Subgroup.card_top] at hodd
  exact hodd h2

omit [Finite G] in
theorem conj_mem_fsuL0 {t : G} (ht : t ∈ T) {y : G} (hy : y ∈ fsuL0 T L) :
    t⁻¹ * y * t ∈ fsuL0 T L := by
  have := (Subgroup.mem_normalizer_iff.mp (SecA.le_fsuM T L (T.inv_mem ht)) y).mp hy
  simpa using this

structure CoordL (T L : Subgroup G) (t : G)
    (Ψ : ↥(fsuL0 T L) →* (↥L ⧸ CFSG.pCore 2 ↥L) × (↥L ⧸ CFSG.pCore 2 ↥L))
    (α : MulAut (↥L ⧸ CFSG.pCore 2 ↥L)) : Prop where
  ker : ∀ y : ↥(fsuL0 T L), Ψ y = 1 ↔ (y : G) ∈ pCoreOf 2 (fsuL0 T L)
  onL : ∀ (l : G) (hl0 : l ∈ fsuL0 T L) (hl : l ∈ L), Ψ ⟨l, hl0⟩ = (mkO2 L l hl, 1)
  swap : ∀ (y : ↥(fsuL0 T L)) (hy : t⁻¹ * y * t ∈ fsuL0 T L),
    Ψ ⟨t⁻¹ * y * t, hy⟩ = (α (Ψ y).2, (Ψ y).1)

namespace CoordL

variable {t : G} {Ψ : ↥(fsuL0 T L) →* (↥L ⧸ CFSG.pCore 2 ↥L) × (↥L ⧸ CFSG.pCore 2 ↥L)}
  {α : MulAut (↥L ⧸ CFSG.pCore 2 ↥L)}

theorem imgIn_T0 (hyp : Hyp10 G T L I) (ht : t ∈ T) (c : CoordL T L t Ψ α) :
    imgIn Ψ (T0 T L) = (D1 T L).prod (D1 T L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hge : (D1 T L).prod (D1 T L) ≤ imgIn Ψ (T0 T L) := by
    rintro ⟨a, b⟩ ⟨ha, hb⟩
    obtain ⟨⟨d₁, hd₁L⟩, hd₁, rfl⟩ := ha
    obtain ⟨⟨d₂, hd₂L⟩, hd₂, rfl⟩ := hb
    have hd₁T : d₁ ∈ T := (Subgroup.mem_subgroupOf.mp hd₁).1
    have hd₂T : d₂ ∈ T := (Subgroup.mem_subgroupOf.mp hd₂).1
    have h0₁ := SecA.le_fsuL0 T L hd₁L
    have h0₂ := SecA.le_fsuL0 T L hd₂L
    have hm₂ := conj_mem_fsuL0 ht h0₂
    have hs : Ψ ⟨t⁻¹ * d₂ * t, hm₂⟩ = (α (Ψ ⟨d₂, h0₂⟩).2, (Ψ ⟨d₂, h0₂⟩).1) :=
      c.swap ⟨d₂, h0₂⟩ hm₂
    refine mem_imgIn.mpr ⟨d₁ * (t⁻¹ * d₂ * t), (fsuL0 T L).mul_mem h0₁ hm₂,
      ⟨T.mul_mem hd₁T (T.mul_mem (T.mul_mem (T.inv_mem ht) hd₂T) ht),
        (fsuL0 T L).mul_mem h0₁ hm₂⟩, ?_⟩
    rw [show (⟨d₁ * (t⁻¹ * d₂ * t), (fsuL0 T L).mul_mem h0₁ hm₂⟩ : ↥(fsuL0 T L)) =
      ⟨d₁, h0₁⟩ * ⟨t⁻¹ * d₂ * t, hm₂⟩ from rfl, map_mul, hs, c.onL d₁ h0₁ hd₁L,
      c.onL d₂ h0₂ hd₂L]
    simp [mkO2]
  have hp : IsPGroup 2 (imgIn Ψ (T0 T L)) := by
    have h2 : IsPGroup 2 (T0 T L) := hyp.fsu.sylow.1.to_le inf_le_left
    exact (h2.of_equiv (Subgroup.subgroupOfEquivOfLe
      (inf_le_right : T0 T L ≤ fsuL0 T L)).symm).map Ψ
  have hodd : ¬ 2 ∣ ((D1 T L).prod (D1 T L)).index := by
    obtain ⟨-, -, h⟩ := isSylowTwoOf_D1 hyp
    have h' : ¬ 2 ∣ (D1 T L).index := by rwa [← Subgroup.relIndex_top_right]
    rw [Subgroup.index_prod]
    intro hd
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp hd with h'' | h'' <;> exact h' h''
  exact eq_of_le_isPGroup hodd hp hge

theorem T0_eq (hyp : Hyp10 G T L I) (ht : t ∈ T) (c : CoordL T L t Ψ α) :
    T0 T L = preIn Ψ ((D1 T L).prod (D1 T L)) := by
  rw [← c.imgIn_T0 hyp ht]
  exact (preIn_imgIn inf_le_right fun x hx =>
    SecA.pCoreOf_fsuL0_le_T0 hyp.fsu.sylow ((c.ker x).mp hx)).symm

theorem map_D1 (hyp : Hyp10 G T L I) (ht : t ∈ T) (c : CoordL T L t Ψ α) :
    (D1 T L).map α.toMonoidHom = D1 T L := by
  have hT := c.imgIn_T0 hyp ht
  have hle : (D1 T L).map α.toMonoidHom ≤ D1 T L := by
    rintro _ ⟨d, hd, rfl⟩
    have h1 : ((1 : ↥L ⧸ CFSG.pCore 2 ↥L), d) ∈ imgIn Ψ (T0 T L) := by
      rw [hT]
      exact ⟨(D1 T L).one_mem, hd⟩
    obtain ⟨y, hy0, hyT, hΨy⟩ := mem_imgIn.mp h1
    have hm := conj_mem_fsuL0 ht hy0
    have hs : Ψ ⟨t⁻¹ * y * t, hm⟩ = (α (Ψ ⟨y, hy0⟩).2, (Ψ ⟨y, hy0⟩).1) :=
      c.swap ⟨y, hy0⟩ hm
    rw [hΨy] at hs
    have h2 : (α d, (1 : ↥L ⧸ CFSG.pCore 2 ↥L)) ∈ imgIn Ψ (T0 T L) :=
      mem_imgIn.mpr ⟨_, hm, ⟨T.mul_mem (T.mul_mem (T.inv_mem ht) hyT.1) ht, hm⟩, hs⟩
    rw [hT] at h2
    exact h2.1
  exact Subgroup.eq_of_le_of_card_ge hle (Subgroup.card_map_of_injective α.injective).ge

theorem le_of_fst_eq_top [IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L)] (hyp : Hyp10 G T L I)
    (c : CoordL T L t Ψ α) (hD1 : D1 T L ≠ ⊥) {Y : Subgroup G} (hT0Y : T0 T L ≤ Y)
    (hA : (imgIn Ψ Y).map (MonoidHom.fst _ _) = ⊤) : L ≤ Y := by
  set N₁ := (imgIn Ψ Y).comap
    (MonoidHom.inl (↥L ⧸ CFSG.pCore 2 ↥L) (↥L ⧸ CFSG.pCore 2 ↥L)) with hN₁def
  have hN₁ : N₁.Normal := ⟨fun x hx g => by
    have hg : g ∈ (imgIn Ψ Y).map (MonoidHom.fst _ _) := hA ▸ Subgroup.mem_top g
    obtain ⟨p, hp, rfl⟩ := hg
    have h := (imgIn Ψ Y).mul_mem ((imgIn Ψ Y).mul_mem hp hx) ((imgIn Ψ Y).inv_mem hp)
    have heq : p * (x, 1) * p⁻¹ = (p.1 * x * p.1⁻¹, 1) := by ext <;> simp
    show (p.1 * x * p.1⁻¹, (1 : ↥L ⧸ CFSG.pCore 2 ↥L)) ∈ imgIn Ψ Y
    rw [← heq]
    exact h⟩
  have hD : ∀ d ∈ T ⊓ L, ∀ hdL : d ∈ L,
      (mkO2 L d hdL, (1 : ↥L ⧸ CFSG.pCore 2 ↥L)) ∈ imgIn Ψ Y := fun d hd hdL =>
    mem_imgIn.mpr ⟨d, SecA.le_fsuL0 T L hdL, hT0Y ⟨hd.1, SecA.le_fsuL0 T L hdL⟩,
      c.onL d _ hdL⟩
  have hN₁ne : N₁ ≠ ⊥ := by
    obtain ⟨⟨q, hq⟩, hq1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hD1
    obtain ⟨⟨d, hdL⟩, hdT, rfl⟩ := hq
    intro hb
    have hmem : mkO2 L d hdL ∈ N₁ := hD d (Subgroup.mem_subgroupOf.mp hdT) hdL
    rw [hb, Subgroup.mem_bot] at hmem
    exact hq1 (Subtype.ext hmem)
  have hN₁top : N₁ = ⊤ := hN₁.eq_bot_or_eq_top.resolve_left hN₁ne
  intro l hl
  have hl0 := SecA.le_fsuL0 T L hl
  have hm : (mkO2 L l hl, (1 : ↥L ⧸ CFSG.pCore 2 ↥L)) ∈ imgIn Ψ Y :=
    (show mkO2 L l hl ∈ N₁ from hN₁top ▸ Subgroup.mem_top _)
  obtain ⟨y, hy0, hyY, hΨy⟩ := mem_imgIn.mp hm
  have hk0 : l * y⁻¹ ∈ fsuL0 T L := (fsuL0 T L).mul_mem hl0 ((fsuL0 T L).inv_mem hy0)
  have hk : l * y⁻¹ ∈ pCoreOf 2 (fsuL0 T L) := by
    apply (c.ker ⟨l * y⁻¹, hk0⟩).mp
    have e1 : (⟨l * y⁻¹, hk0⟩ : ↥(fsuL0 T L)) = ⟨l, hl0⟩ * ⟨y, hy0⟩⁻¹ := rfl
    rw [e1, map_mul, map_inv, hΨy, c.onL l hl0 hl, mul_inv_cancel]
  have := Y.mul_mem (hT0Y (SecA.pCoreOf_fsuL0_le_T0 hyp.fsu.sylow hk)) hyY
  simpa using this

end CoordL

end CFSG.Quasithin.Vol2.Ch10.SecB
