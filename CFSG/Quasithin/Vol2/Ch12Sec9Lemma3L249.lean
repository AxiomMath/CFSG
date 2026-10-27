module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma3Dyn
public import CFSG.Walter.PSL2Facts.Odd
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma3Cs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

namespace L1293D

theorem exists_psl2 {X : Type} [Group X] {p e : ℕ} (h : IsPSL 2 p e X) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ e ∧
      Nonempty (X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := by
  obtain ⟨-, F, hF, hfin, hc, ⟨e⟩⟩ := h
  exact ⟨F, hF, hfin, hc, ⟨e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 F).symm⟩⟩

theorem neg_one_ne_one {F : Type} [Field F] [Finite F] {e : ℕ} (hF : Nat.card F = 7 ^ e) :
    (-1 : F) ≠ 1 := by
  classical
  let := Fintype.ofFinite F
  intro h
  have h2 : (2 : F) = 0 := by
    have : (1 : F) + 1 = 0 := by
      calc (1 : F) + 1 = -1 + 1 := by rw [h]
        _ = 0 := neg_add_cancel 1
    rw [← this]
    norm_num
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : addOrderOf (1 : F) = 2 :=
    addOrderOf_eq_prime (by rw [two_nsmul]; exact (by simpa [one_add_one_eq_two] using h2))
      one_ne_zero
  have hdvd := addOrderOf_dvd_natCard (1 : F)
  rw [h1, hF] at hdvd
  exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_two hdvd) (by norm_num)

theorem card_psl2 {F : Type} [Field F] [Finite F] {e : ℕ} (hF : Nat.card F = 7 ^ e) :
    Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) * 2 =
      Nat.card F * (Nat.card F ^ 2 - 1) := by
  have h := BenderSuzuki.External.huppert614_card_psl_mul_center (K := F)
  rwa [BenderSuzuki.External.huppert614_card_center_of_neg_one_ne_one (neg_one_ne_one hF)] at h

variable {X : Type} [Group X] [Finite X]

theorem pCoreOf_eq_bot {B : Subgroup X} (hs : IsSimpleGroup ↥B) (h168 : Nat.card B = 168) :
    pCoreOf 2 B = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := pCoreOf 2 B with hP
  have hPB : P ≤ B := LieType.BorelTits.pCoreOf_le 2 B
  have hn : (P.subgroupOf B).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPB).2
      (LieType.BorelTits.le_normalizer_pCoreOf 2 B)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (P.subgroupOf B) with h | h
  · rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hPB hx⟩ : B) ∈ P.subgroupOf B := Subgroup.mem_subgroupOf.2 hx
    rw [h, Subgroup.mem_bot] at this
    exact (Subgroup.mem_bot).2 (congrArg Subtype.val this)
  · exfalso
    have hBP : B ≤ P := fun x hx => by
      have : (⟨x, hx⟩ : B) ∈ P.subgroupOf B := by rw [h]; exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.1 this
    obtain ⟨k, hk⟩ := (LieType.BorelTits.pCoreOf_isPGroup 2 B).exists_card_eq
    have hle := Subgroup.card_dvd_of_le hBP
    rw [h168, hk] at hle
    have h3 : 3 ∣ 2 ^ k := (by norm_num : 3 ∣ 168).trans hle
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)

theorem dynkinL249 {B K S : Subgroup X} (hBK : B ≤ K) (hB : IsPSL 2 7 1 ↥B)
    (hK : IsPSL 2 7 2 ↥K) (hS : QuasithinUnique.IsSylowTwoOf S K) :
    ∃ s ∈ S, KbarInducesOuter B s := by
  classical
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨F₁, _, _, hF₁, ⟨e₁⟩⟩ := exists_psl2 hB
  obtain ⟨F₂, _, _, hF₂, ⟨e₂⟩⟩ := exists_psl2 hK
  have hB168 : Nat.card B = 168 := by
    have := card_psl2 hF₁
    rw [hF₁] at this
    rw [Nat.card_congr e₁.toEquiv]
    omega
  have hK58800 : Nat.card K = 58800 := by
    have := card_psl2 hF₂
    rw [hF₂] at this
    rw [Nat.card_congr e₂.toEquiv]
    omega
  have hBs : IsSimpleGroup ↥B := by
    have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F₁) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [hF₁]; norm_num)
    exact e₁.isSimpleGroup
  have hO2 := pCoreOf_eq_bot hBs hB168
  have hZB : ∀ b ∈ B, (∀ x ∈ B, b * x = x * b) → b = 1 := by
    intro b hb hc
    have hZ : Subgroup.center ↥B = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥B) with h | h
      · exact h
      · exfalso
        have hab : ∀ x y : ↥B, x * y = y * x := fun x y =>
          (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top x) y).symm
        obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥B) 2 (by rw [hB168]; norm_num)
        have hn : (Subgroup.zpowers x).Normal := ⟨fun y _ g => by
          rwa [hab g y, mul_assoc, mul_inv_cancel, mul_one]⟩
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers x) with h1 | h1
        · have : x = 1 := by
            have := Subgroup.mem_zpowers x
            rw [h1, Subgroup.mem_bot] at this
            exact this
          rw [this, orderOf_one] at hx
          norm_num at hx
        · have := Nat.card_zpowers x
          rw [h1, Subgroup.card_top, hx, hB168] at this
          norm_num at this
    have : (⟨b, hb⟩ : B) ∈ Subgroup.center ↥B :=
      Subgroup.mem_center_iff.2 fun y => Subtype.ext (hc y y.2).symm
    rw [hZ, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  obtain ⟨hSK, hS2, hidx⟩ := hS
  have hS16 : Nat.card S = 16 := by
    obtain ⟨k, hk⟩ := hS2.exists_card_eq
    have h1 := (S.subgroupOf K).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSK).toEquiv, hk, hK58800] at h1
    have hodd : ¬ 2 ∣ (S.subgroupOf K).index := hidx
    have hk4 : k = 4 := by
      have h2 : 2 ^ k ∣ 2 ^ 4 * 3675 := Dvd.intro _ (by rw [h1]; norm_num)
      have h3 : 2 ^ 4 ∣ 2 ^ k * (S.subgroupOf K).index := Dvd.intro 3675 (by rw [h1]; norm_num)
      have hc1 : Nat.Coprime (2 ^ k) 3675 := Nat.Coprime.pow_left k (by norm_num)
      have hc2 : Nat.Coprime (2 ^ 4) (S.subgroupOf K).index :=
        Nat.Coprime.pow_left 4 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd)
      exact le_antisymm ((Nat.pow_dvd_pow_iff_le_right (by norm_num)).1
        (hc1.dvd_of_dvd_mul_right h2)) ((Nat.pow_dvd_pow_iff_le_right (by norm_num)).1
        (hc2.dvd_of_dvd_mul_right h3))
    rw [hk, hk4]
    norm_num
  by_contra hall
  simp only [KbarInducesOuter, not_exists, not_and, not_forall, not_not] at hall
  set C := K ⊓ Subgroup.centralizer (B : Set X) with hC
  have hdec : ∀ s ∈ S, ∃ b ∈ B, s * b⁻¹ ∈ C := by
    intro s hs
    obtain ⟨b, hb, hall'⟩ := hall s hs
    refine ⟨b, hb, K.mul_mem (hSK hs) (K.inv_mem (hBK hb)), ?_⟩
    show s * b⁻¹ ∈ Subgroup.centralizer (B : Set X)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 := hall' x hx
    rw [hO2, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  have hinf : ∀ x ∈ C, x ∈ B → x = 1 := fun x hxC hxB => hZB x hxB fun y hy =>
    (Subgroup.mem_centralizer_iff.1 hxC.2 y hy).symm
  let f : ↥C × ↥B →* X := MonoidHom.noncommCoprod C.subtype B.subtype
    (fun c b => (Subgroup.mem_centralizer_iff.1 c.2.2 b b.2).symm)
  have hf : ∀ c b, f (c, b) = (c : X) * b := fun c b => rfl
  have hfinj : Function.Injective f := by
    rintro ⟨⟨c, hc⟩, ⟨b, hb⟩⟩ ⟨⟨c', hc'⟩, ⟨b', hb'⟩⟩ h
    have h0 : c * b = c' * b' := h
    have h1 : c'⁻¹ * c = b' * b⁻¹ := by
      calc c'⁻¹ * c = c'⁻¹ * (c * b) * b⁻¹ := by group
        _ = c'⁻¹ * (c' * b') * b⁻¹ := by rw [h0]
        _ = b' * b⁻¹ := by group
    have h2 := hinf _ (C.mul_mem (C.inv_mem hc') hc) (h1 ▸ B.mul_mem hb' (B.inv_mem hb))
    have hcc : c = c' := by
      rw [inv_mul_eq_one] at h2
      exact h2.symm
    have hbb : b = b' := by
      rw [hcc] at h0
      exact mul_left_cancel h0
    subst hcc hbb
    rfl
  have hSf : S ≤ f.range := by
    intro s hs
    obtain ⟨b, hb, hsb⟩ := hdec s hs
    exact ⟨(⟨s * b⁻¹, hsb⟩, ⟨b, hb⟩), by rw [hf]; group⟩
  have hcard : Nat.card f.range = Nat.card C * 168 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv, Nat.card_prod, hB168]
  have h16 := Subgroup.card_dvd_of_le hSf
  rw [hS16, hcard] at h16
  have h2C : 2 ∣ Nat.card C := by omega
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := C) 2 h2C
  have htK : (t : X) ∈ K := t.2.1
  have htB : ∀ x ∈ B, x * t = t * x := fun x hx => Subgroup.mem_centralizer_iff.1 t.2.2 x hx
  set t' := e₂ ⟨t, htK⟩ with ht'
  have ht'2 : orderOf t' = 2 := by
    rw [ht', MulEquiv.orderOf_eq, Subgroup.orderOf_mk, Subgroup.orderOf_coe, ht]
  have h48 := ((CFSG.Walter.psl2_centralizer_involution F₂ hF₂ (by decide) (by norm_num)
    ht'2).1 (by norm_num)).1
  let g : ↥B →*
      Subgroup.centralizer ({t'} : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F₂)) :=
    { toFun := fun b => ⟨e₂ ⟨b, hBK b.2⟩, by
        rw [Subgroup.mem_centralizer_iff]
        rintro _ rfl
        rw [ht', ← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (htB b b.2).symm⟩
      map_one' := by
        apply Subtype.ext
        simp only [OneMemClass.coe_one]
        rw [← map_one e₂]
        rfl
      map_mul' := fun a b => by
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        rw [← map_mul]
        rfl }
  have hginj : Function.Injective g := fun a b h => by
    have := congrArg Subtype.val h
    have h' := e₂.injective this
    exact Subtype.ext (congrArg (fun y : ↥K => (y : X)) h')
  have hle := Nat.card_le_card_of_injective g hginj
  rw [hB168, h48] at hle
  norm_num at hle

end L1293D

theorem dynkinFact1293_of (h : DynkinFact1293SL3) : DynkinFact1293 := by
  intro X _ _ B K S hBK hpair hS hSB
  rcases hpair with ⟨hB, hK⟩ | ⟨hB, hK⟩
  · exact L1293D.dynkinL249 hBK hB hK hS
  · exact h X B K S hBK hB hK hS hSB

end CFSG.Quasithin.H13
