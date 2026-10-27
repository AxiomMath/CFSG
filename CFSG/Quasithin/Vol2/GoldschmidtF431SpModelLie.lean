module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Setting
public import CFSG.Quasithin.Vol2.GoldschmidtF431SpModel
public import CFSG.Quasithin.Recognition.CertTwoLocal

public section

namespace CFSG.Quasithin.H13.F431

open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Borel252 CFSG.Open
  CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis

section Swap

theorem BorelData.symm' {M : Type} [Group M] {U R₁ R₂ : Subgroup M} (h : BorelData M U R₁ R₂) :
    BorelData M U R₂ R₁ where
  center_trivial := h.center_trivial
  sylow := h.sylow
  le₁ := h.le₂
  le₂ := h.le₁
  sup := by rw [sup_comm]; exact h.sup
  cent₁ := h.cent₂
  cent₂ := h.cent₁
  lt₁ := h.lt₂
  lt₂ := h.lt₁
  lt_top₁ := h.lt_top₂
  lt_top₂ := h.lt_top₁
  core₁ := h.core₂
  core₂ := h.core₁
  only := fun X hX hXt => (h.only X hX hXt).symm

variable {G : Type*} [Group G]

theorem SpShape.swap {T : Subgroup G} {Q : Fin 2 → Subgroup G} (S : SpShape T Q) :
    SpShape T ![Q 1, Q 0] where
  Q_le j := by
    fin_cases j
    · exact S.Q_le 1
    · exact S.Q_le 0
  Q_norm j := by
    fin_cases j
    · exact S.Q_norm 1
    · exact S.Q_norm 0
  Q_abel j := by
    fin_cases j
    · exact S.Q_abel 1
    · exact S.Q_abel 0
  Z_le j := by
    fin_cases j
    · exact S.Z_le 1
    · exact S.Z_le 0
  Z_sq := S.Z_sq
  inv_mem := by
    intro x hx hx2
    obtain ⟨j, hj⟩ := S.inv_mem x hx hx2
    fin_cases j
    · exact ⟨1, hj⟩
    · exact ⟨0, hj⟩
  cen := by
    intro j x hx hxZ y hy hxy
    fin_cases j
    · exact S.cen 1 x hx hxZ y hy hxy
    · exact S.cen 0 x hx hxZ y hy hxy
  ex := by
    intro j
    fin_cases j
    · exact S.ex 1
    · exact S.ex 0

end Swap

theorem SpDData.swap {D : Type} [Group D] {U : Subgroup D} {R : Fin 2 → Subgroup D}
    {i : Fin 3 → D} (h : SpDData U R i) : SpDData U ![R 1, R 0] ![i 1, i 0, i 2] where
  borel := BorelData.symm' h.borel
  shape := h.shape.swap
  Z_le j := by
    fin_cases j
    · exact h.Z_le 1
    · exact h.Z_le 0
  Z_ne j := by
    fin_cases j
    · exact h.Z_ne 1
    · exact h.Z_ne 0
  Z_trans j := by
    fin_cases j
    · exact h.Z_trans 1
    · exact h.Z_trans 0
  Z_inf x h0 h1 := h.Z_inf x h1 h0
  i_mem k := by
    fin_cases k
    · exact h.i_mem 1
    · exact h.i_mem 0
    · exact h.i_mem 2
  i_ne k := by
    fin_cases k
    · exact h.i_ne 1
    · exact h.i_ne 0
    · exact h.i_ne 2
  i_sq k := by
    fin_cases k
    · exact h.i_sq 1
    · exact h.i_sq 0
    · exact h.i_sq 2
  i0 := h.i1
  i1 := h.i0
  i2 := ⟨h.i2.2, h.i2.1⟩
  cent0 := h.cent1
  cent1 := h.cent0
  cent2 := h.cent2
  fus := by
    intro x hx hx1 hx2
    obtain ⟨k, j, m, hm, hmx⟩ := h.fus x hx hx1 hx2
    refine ⟨![1, 0, 2] k, ![1, 0] j, m, ?_, ?_⟩
    · fin_cases j
      · exact hm
      · exact hm
    · fin_cases k
      · exact hmx
      · exact hmx
      · exact hmx

section Amalgam

open SpModel

theorem exists_equiv_antiSp {D : Type} [Group D] {f : ℕ} (hD : LieModel D .PSp 2 2 f) :
    2 ≤ f ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
      Nat.card F = 2 ^ f ∧ Nonempty (D ≃* antiSp F) := by
  rcases hD with ⟨-, hM⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · obtain ⟨hadm, K, hKf, hKfin, hKcard, ⟨e⟩⟩ := hM
    have hf1 : 1 ≤ f := hadm.2.1
    have hf2 : f ≠ 1 := by
      rintro rfl
      exact hadm.2.2.2 (by simp)
    have hchar : CharP K 2 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have := Fintype.ofFinite K
      exact charP_of_card_eq_prime_pow (p := 2) (f := f)
        (by rw [← Nat.card_eq_fintype_card]; exact hKcard)
    exact ⟨by omega, K, hKf, hKfin, hchar, hKcard, ⟨e.trans (antiProjEquiv K).symm⟩⟩
  all_goals exact absurd h0 (by norm_num)

theorem spAmalgam_data {D : Type} [Group D] {f : ℕ} (hD : LieModel D .PSp 2 2 f)
    (A : LieAmalgamExt D) :
    2 ≤ f ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (E : D ≃* antiSp F) (R : Fin 2 → Subgroup (antiSp F)) (i : Fin 3 → antiSp F),
      Nat.card F = 2 ^ f ∧ SpDData (antiUnipotent F) R i ∧
      A.P1.map E.toMonoidHom = Subgroup.normalizer (R 0 : Set (antiSp F)) ∧
      A.P2.map E.toMonoidHom = Subgroup.normalizer (R 1 : Set (antiSp F)) := by
  obtain ⟨hf, F, hFf, hFfin, hFchar, hFcard, ⟨e1⟩⟩ := exists_equiv_antiSp hD
  have hy1 := A.yam.map e1
  have hU := (borel_antiSp (F := F) hf hFcard).sylow
  obtain ⟨h, -, hh⟩ := IsSylowTwoOf.exists_conj hy1.1 hU
  let E : D ≃* antiSp F := e1.trans (MulAut.conj h)
  have hy2 : IsYAmalgamPair (antiUnipotent F) (A.P1.map E.toMonoidHom)
      (A.P2.map E.toMonoidHom) := by
    have := A.yam.map E
    have hTD : A.TD.map E.toMonoidHom = antiUnipotent F := by
      rw [hh, Subgroup.map_map]
      rfl
    rwa [hTD] at this
  refine ⟨hf, F, hFf, hFfin, hFchar, E, ?_⟩
  rcases yam_antiSp hf hFcard hy2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨Rrad F, iRep F, hFcard, spDData_antiSp hf hFcard, h1, h2⟩
  · exact ⟨![radA2 F, radA1 F], ![iRep F 1, iRep F 0, iRep F 2], hFcard,
      (spDData_antiSp hf hFcard).swap, h1, h2⟩

theorem f431ModelFacts_psp (f : ℕ) : F431ModelFacts .PSp 2 f := by
  intro D _ hD
  obtain ⟨hf, F, hFf, hFfin, hFchar, hFcard, ⟨e⟩⟩ := exists_equiv_antiSp hD
  refine ⟨Finite.of_injective e e.injective, ?_⟩
  rw [eq_bot_iff]
  intro d hd
  rw [Subgroup.mem_bot]
  have hB := borel_antiSp (F := F) hf hFcard
  apply e.injective
  rw [map_one]
  apply hB.center_trivial
  intro y
  obtain ⟨x, rfl⟩ := e.surjective y
  have := Subgroup.mem_center_iff.mp hd x
  rw [← map_mul, ← map_mul, this]

section Gen

variable {D : Type} [Group D]

theorem conj_mem_autStab {P : Subgroup D} {p : D} (hp : p ∈ P) :
    (MulAut.conj p : MulAut D) ∈ autStab P := fun x => by
  rw [MulAut.conj_apply]
  constructor
  · intro hx
    exact P.mul_mem (P.mul_mem hp hx) (P.inv_mem hp)
  · intro hx
    have := P.mul_mem (P.mul_mem (P.inv_mem hp) hx) hp
    simpa [mul_assoc] using this

theorem map_conj_le_N1 (A : LieAmalgamExt D) :
    A.P1.map (MulAut.conj : D →* MulAut D) ≤ A.N1 := by
  rintro _ ⟨p, hp, rfl⟩
  exact ⟨A.inn_le ⟨p, rfl⟩, conj_mem_autStab hp⟩

theorem map_conj_le_N2 (A : LieAmalgamExt D) :
    A.P2.map (MulAut.conj : D →* MulAut D) ≤ A.N2 := by
  rintro _ ⟨p, hp, rfl⟩
  exact ⟨A.inn_le ⟨p, rfl⟩, conj_mem_autStab hp⟩

theorem range_conj_le_K (A : LieAmalgamExt D) (hsup : A.P1 ⊔ A.P2 = ⊤) :
    (MulAut.conj : D →* MulAut D).range ≤ A.K := by
  have h : (⊤ : Subgroup D).map (MulAut.conj : D →* MulAut D) ≤ A.K := by
    rw [← hsup, Subgroup.map_sup]
    exact sup_le ((map_conj_le_N1 A).trans A.N1_le_K) ((map_conj_le_N2 A).trans A.N2_le_K)
  rintro _ ⟨d, rfl⟩
  exact h ⟨d, Subgroup.mem_top d, rfl⟩

theorem sup_eq_top_psp {f : ℕ} (hD : LieModel D .PSp 2 2 f) (A : LieAmalgamExt D) :
    A.P1 ⊔ A.P2 = ⊤ := by
  obtain ⟨hf, F, hFf, hFfin, hFchar, E, R, i, hFcard, hDd, h1, h2⟩ := spAmalgam_data hD A
  have hmap : (A.P1 ⊔ A.P2).map E.toMonoidHom = ⊤ := by
    rw [Subgroup.map_sup, h1, h2]
    exact hDd.borel.sup_norm
  rw [eq_top_iff]
  intro x _
  have hx : E x ∈ (A.P1 ⊔ A.P2).map E.toMonoidHom := by rw [hmap]; exact Subgroup.mem_top _
  obtain ⟨y, hy, hyx⟩ := hx
  have : y = x := E.injective hyx
  rwa [this] at hy

theorem f431Generation_psp (f : ℕ) : F431Generation .PSp 2 f := by
  intro D _ hD A
  exact range_conj_le_K A (sup_eq_top_psp hD A)

end Gen

section Lift

variable {D : Type} [Group D]

theorem mulAut_conj_conj (φ : MulAut D) (d : D) : φ * MulAut.conj d * φ⁻¹ = MulAut.conj (φ d) := by
  ext z
  simp [MulAut.conj_apply]

theorem mem_autStab_iff_of_normalizer {S : Subgroup D}
    (hS : pCoreOf 2 (Subgroup.normalizer (S : Set D)) = S) (φ : MulAut D) :
    φ ∈ autStab (Subgroup.normalizer (S : Set D)) ↔ ∀ x, x ∈ S ↔ φ x ∈ S := by
  constructor
  · intro h x
    have hmap : (Subgroup.normalizer (S : Set D)).map φ.toMonoidHom =
        Subgroup.normalizer (S : Set D) := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact (h z).mp hz
      · intro hy
        refine ⟨φ⁻¹ y, ?_, by simp⟩
        exact (h (φ⁻¹ y)).mpr (by simpa using hy)
    have hS' : S.map φ.toMonoidHom = S := by
      have := pCoreOf_map_of_injective φ.toMonoidHom φ.injective (Subgroup.normalizer (S : Set D))
      rw [hmap, hS] at this
      exact this.symm
    constructor
    · intro hx
      have : φ x ∈ S.map φ.toMonoidHom := ⟨x, hx, rfl⟩
      rwa [hS'] at this
    · intro hx
      rw [← hS'] at hx
      obtain ⟨z, hz, hzx⟩ := hx
      have : z = x := φ.injective hzx
      rwa [this] at hz
  · intro hφ x
    rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
    constructor
    · intro h y
      have e : φ (x * φ⁻¹ y * x⁻¹) = φ x * y * (φ x)⁻¹ := by simp
      calc y ∈ S ↔ φ⁻¹ y ∈ S := by
            have := hφ (φ⁻¹ y)
            simpa using this.symm
        _ ↔ x * φ⁻¹ y * x⁻¹ ∈ S := h _
        _ ↔ φ (x * φ⁻¹ y * x⁻¹) ∈ S := hφ _
        _ ↔ φ x * y * (φ x)⁻¹ ∈ S := by rw [e]
    · intro h y
      have e : φ (x * y * x⁻¹) = φ x * φ y * (φ x)⁻¹ := by simp
      calc y ∈ S ↔ φ y ∈ S := hφ y
        _ ↔ φ x * φ y * (φ x)⁻¹ ∈ S := h (φ y)
        _ ↔ φ (x * y * x⁻¹) ∈ S := by rw [e]
        _ ↔ x * y * x⁻¹ ∈ S := (hφ _).symm

theorem mem_normalizer_map_codRestrict_iff {K : Subgroup (MulAut D)}
    (hK : ∀ d : D, MulAut.conj d ∈ K) (hinj : Function.Injective (MulAut.conj : D →* MulAut D))
    (S : Subgroup D) (x : ↥K) :
    x ∈ Subgroup.normalizer
        ((S.map ((MulAut.conj : D →* MulAut D).codRestrict K hK) : Subgroup ↥K) : Set ↥K) ↔
      ∀ d, d ∈ S ↔ (x : MulAut D) d ∈ S := by
  set Φ := (MulAut.conj : D →* MulAut D).codRestrict K hK with hΦ
  have hΦinj : Function.Injective Φ := fun a b h => hinj (congrArg Subtype.val h)
  have hconj : ∀ (x : ↥K) (d : D), x * Φ d * x⁻¹ = Φ ((x : MulAut D) d) := fun x d =>
    Subtype.ext (by
      show (x : MulAut D) * MulAut.conj d * (x : MulAut D)⁻¹ = MulAut.conj ((x : MulAut D) d)
      exact mulAut_conj_conj _ _)
  rw [Subgroup.mem_normalizer_iff]
  constructor
  · intro h d
    have := h (Φ d)
    rw [Subgroup.mem_map_iff_mem hΦinj, hconj, Subgroup.mem_map_iff_mem hΦinj] at this
    exact this
  · intro h y
    constructor
    · rintro ⟨s, hs, rfl⟩
      rw [hconj]
      exact ⟨_, (h s).mp hs, rfl⟩
    · rintro ⟨s', hs', hy⟩
      have e1 : y = x⁻¹ * (x * y * x⁻¹) * x := by group
      have e2 : x⁻¹ * Φ s' * x⁻¹⁻¹ = Φ (((x⁻¹ : ↥K) : MulAut D) s') := hconj x⁻¹ s'
      have hs'' : ((x⁻¹ : ↥K) : MulAut D) s' ∈ S := by
        have := (h (((x⁻¹ : ↥K) : MulAut D) s')).mpr
        apply this
        have e3 : (x : MulAut D) (((x⁻¹ : ↥K) : MulAut D) s') = s' := by
          show (x : MulAut D) ((x : MulAut D)⁻¹ s') = s'
          simp
        rw [e3]
        exact hs'
      refine ⟨_, hs'', ?_⟩
      rw [← e2, inv_inv, hy]
      group

theorem codRestrict_conj_conj {K : Subgroup (MulAut D)} (hK : ∀ d : D, MulAut.conj d ∈ K)
    (x : ↥K) (d : D) :
    x * (MulAut.conj : D →* MulAut D).codRestrict K hK d * x⁻¹ =
      (MulAut.conj : D →* MulAut D).codRestrict K hK ((x : MulAut D) d) :=
  Subtype.ext (by
    show (x : MulAut D) * MulAut.conj d * (x : MulAut D)⁻¹ = MulAut.conj ((x : MulAut D) d)
    exact mulAut_conj_conj _ _)

end Lift

end Amalgam

section Main

open SpModel

theorem f431SpLieProp (f : ℕ) : F431SpLieProp f := by
  intro D _ hD A hodd
  obtain ⟨hf, F, hFf, hFfin, hFchar, E, R, i, hFcard, hDd, h1, h2⟩ := spAmalgam_data hD A
  have hfinD : Finite D := Finite.of_injective E E.injective
  have hfinX : Finite (antiSp F) := Finite.of_equiv D E.toEquiv
  have hfinAut : Finite (MulAut D) := finite_mulAut_of_finite
  have hgen := f431Generation_psp f D hD A
  have hK : ∀ d : D, (MulAut.conj d : MulAut D) ∈ A.K := fun d => hgen ⟨d, rfl⟩
  have hcen := (f431ModelFacts_psp f D hD).2
  have hinj : Function.Injective (MulAut.conj : D →* MulAut D) := by
    rw [injective_iff_map_eq_one]
    intro d hd
    have hdc : d ∈ Subgroup.center D := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := congrArg (fun φ : MulAut D => φ g) hd
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this.symm
    rw [hcen] at hdc
    exact Subgroup.mem_bot.mp hdc
  set ΦD : D →* ↥A.K := (MulAut.conj : D →* MulAut D).codRestrict A.K hK with hΦD
  set Φ : antiSp F →* ↥A.K := ΦD.comp E.symm.toMonoidHom with hΦ
  have hΦD_inj : Function.Injective ΦD := fun a b h => hinj (congrArg Subtype.val h)
  have hΦinj : Function.Injective Φ := hΦD_inj.comp E.symm.injective
  have hrange : Φ.range = ΦD.range := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨E.symm x, rfl⟩
    · rintro ⟨d, rfl⟩
      exact ⟨E d, by simp [hΦ]⟩
  have hnorm : Φ.range.Normal := by
    rw [hrange]
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨d, rfl⟩ := hn
    exact ⟨(g : MulAut D) d, (codRestrict_conj_conj hK g d).symm⟩
  have hindex : Odd Φ.range.index := by
    have hcard := Subgroup.card_mul_index Φ.range
    have hrc : Nat.card Φ.range = Nat.card D := by
      rw [← Nat.card_congr (MonoidHom.ofInjective hΦinj).toEquiv]
      exact Nat.card_congr E.symm.toEquiv
    rw [hrc] at hcard
    have hpos : 0 < Nat.card D := Nat.card_pos
    have : Φ.range.index = Nat.card ↥A.K / Nat.card D := by
      rw [← hcard, Nat.mul_div_cancel_left _ hpos]
    rw [this]
    exact hodd
  have key : ∀ (P : Subgroup D) (r : Subgroup (antiSp F)) (N' : Subgroup ↥A.K),
      P.map E.toMonoidHom = Subgroup.normalizer (r : Set (antiSp F)) →
      pCoreOf 2 (Subgroup.normalizer (r : Set (antiSp F))) = r →
      (∀ x : ↥A.K, x ∈ N' ↔ (x : MulAut D) ∈ autStab P) →
      N' = Subgroup.normalizer ((r.map Φ : Subgroup ↥A.K) : Set ↥A.K) := by
    intro P r N' hP hcore hN'
    set S : Subgroup D := r.map E.symm.toMonoidHom with hS
    have hnS : (Subgroup.normalizer (r : Set (antiSp F))).map E.symm.toMonoidHom =
        Subgroup.normalizer (S : Set D) := by
      ext g
      rw [Subgroup.mem_map_equiv, hS, mem_normalizer_map E.symm r g]
    have hPS : P = Subgroup.normalizer (S : Set D) := by
      rw [← hnS, ← hP, Subgroup.map_map]
      ext g
      simp
    have hcoreS : pCoreOf 2 (Subgroup.normalizer (S : Set D)) = S := by
      rw [← hnS, pCoreOf_map_of_injective E.symm.toMonoidHom E.symm.injective, hcore]
    have hrS : r.map Φ = S.map ΦD := by
      rw [hS, Subgroup.map_map]
    ext x
    rw [hN' x, hrS, mem_normalizer_map_codRestrict_iff hK hinj S x, hPS,
      mem_autStab_iff_of_normalizer hcoreS]
  have hKM : ∀ x : ↥A.K, (x : MulAut D) ∈ A.Mbar := fun x => (sup_le inf_le_left inf_le_left :
    A.K ≤ A.Mbar) x.2
  have hN : ∀ j : Fin 2, (![A.Mb1, A.Mb2] : Fin 2 → Subgroup ↥A.K) j =
      Subgroup.normalizer ((((R j).map Φ : Subgroup ↥A.K)) : Set ↥A.K) := by
    intro j
    fin_cases j
    · refine key A.P1 (R 0) A.Mb1 h1 hDd.borel.core₁ ?_
      intro x
      rw [Subgroup.mem_subgroupOf]
      exact ⟨fun hx => hx.2, fun hx => ⟨hKM x, hx⟩⟩
    · refine key A.P2 (R 1) A.Mb2 h2 hDd.borel.core₂ ?_
      intro x
      rw [Subgroup.mem_subgroupOf]
      exact ⟨fun hx => hx.2, fun hx => ⟨hKM x, hx⟩⟩
  have : Φ.range.Normal := hnorm
  exact exists_spLie_of_data Φ hΦinj hindex hDd ![A.Mb1, A.Mb2] hN

end Main

end CFSG.Quasithin.H13.F431
