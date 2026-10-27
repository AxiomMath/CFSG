module

public import CFSG.Quasithin.EmptyFaithful.S146zRL3Set
public import CFSG.Quasithin.EmptyFaithful.S146zRSyl
public import CFSG.Quasithin.EmptyFaithful.S146zRSLA
public import CFSG.Quasithin.EmptyFaithful.S146zRSLB
public import CFSG.Quasithin.EmptyFaithful.S14612DB

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped Pointwise MatrixGroups

section TwoClosed

variable {X : Type} [Group X] {N₁ N₂ : Subgroup X} {ŝ : X}

theorem q_hat_normalizes_U [Finite X] (hF : CaseIFacts N₁ N₂ ŝ) {That Hhat Khat : Subgroup X}
    (hSyl : IsSylowTwoOf That (⊤ : Subgroup X)) (hTH : That ≤ Hhat) (hKH : Khat ≤ Hhat)
    (hKN : Khat ≤ N₁ ⊔ N₂) (hHs : Group.IsSolvable ↥Hhat)
    (hdec : ∀ x ∈ Hhat, ∃ k ∈ Khat, ∃ t ∈ That, x = k * t)
    (hP₁ : ∀ A : Subgroup X, A ≤ N₁ → That ⊓ N₁ ≤ A → Group.IsSolvable ↥A →
      A ≤ Subgroup.normalizer ((That ⊓ N₁ : Subgroup X) : Set X))
    (hP₂ : ∀ A : Subgroup X, A ≤ N₂ → That ⊓ N₂ ≤ A → Group.IsSolvable ↥A →
      A ≤ Subgroup.normalizer ((That ⊓ N₂ : Subgroup X) : Set X)) :
    ∀ x ∈ Hhat, x ∈ Subgroup.normalizer ((That ⊓ (N₁ ⊔ N₂) : Subgroup X) : Set X) := by
  have hEq := q_inf_sup_eq hF hSyl
  intro x hx
  obtain ⟨k, hk, t, ht, rfl⟩ := hdec x hx
  have hDs : Group.IsSolvable ↥(Hhat ⊓ (N₁ ⊔ N₂)) :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion (inf_le_left :
      Hhat ⊓ (N₁ ⊔ N₂) ≤ Hhat)) (Subgroup.inclusion_injective _)
  have hU : (That ⊓ N₁) ⊔ (That ⊓ N₂) ≤ Hhat ⊓ (N₁ ⊔ N₂) := sup_le
    (le_inf (inf_le_left.trans hTH) (inf_le_right.trans le_sup_left))
    (le_inf (inf_le_left.trans hTH) (inf_le_right.trans le_sup_right))
  have hD := q_two_closed_prod N₁ N₂ hF.comm hF.disj (That ⊓ N₁) (That ⊓ N₂) inf_le_right
    inf_le_right hP₁ hP₂ (Hhat ⊓ (N₁ ⊔ N₂)) inf_le_right hDs hU
  have hk' : k ∈ Subgroup.normalizer ((That ⊓ (N₁ ⊔ N₂) : Subgroup X) : Set X) := by
    rw [hEq]
    exact hD ⟨hKH hk, hKN hk⟩
  have hN : t ∈ Subgroup.normalizer ((N₁ ⊔ N₂ : Subgroup X) : Set X) :=
    (Subgroup.normalizer_eq_top_iff.mpr hF.normal) ▸ Subgroup.mem_top t
  have ht' : t ∈ Subgroup.normalizer ((That ⊓ (N₁ ⊔ N₂) : Subgroup X) : Set X) :=
    q_mem_normalizer_inf (Subgroup.le_normalizer ht) hN
  exact (Subgroup.normalizer _).mul_mem hk' ht'

end TwoClosed

section SimpleSL2

theorem q_center_sl2_char_two {F : Type*} [Field F] [CharP F 2] :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨r, hr, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
  have hr2 : r ^ 2 = 1 := by simpa using hr
  have hchar : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have h1 : (r - 1) ^ 2 = 0 := by linear_combination hr2 + (1 - r) * hchar
  have h2 : r = 1 := sub_eq_zero.mp (pow_eq_zero_iff (two_ne_zero) |>.mp h1)
  subst h2
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hrz]
  simp

theorem q_isSimpleGroup_sl2 {F : Type} [Field F] [Finite F] [CharP F 2] (hq : 4 ≤ Nat.card F) :
    IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) F) := by
  have h : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hq
  let e : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    (QuotientGroup.quotientMulEquivOfEq q_center_sl2_char_two).trans QuotientGroup.quotientBot
  exact e.symm.isSimpleGroup

theorem q_nonabelian_sl2 {F : Type} [Field F] [Finite F] [CharP F 2] (hq : 4 ≤ Nat.card F) :
    ∃ a b : Matrix.SpecialLinearGroup (Fin 2) F, a * b ≠ b * a := by
  by_contra h
  push Not at h
  exact SL2Sylow.not_isSolvable_sl2 hq (Group.isSolvable_of_comm h)

end SimpleSL2

section Setting

variable {G : Type} [Group G] [Finite G] {T M H PQ : Subgroup G} {p : ℕ}

theorem q_hatH_solvable (S : Setting146 G T M) (hred : IsRedCE T M H PQ p) :
    Group.IsSolvable ↥(imageOTwoQuot (mcOf T) H) := by
  have hHG : H ≤ mcOf T := S.le_mcOf hred.isHTM
  have hHs : Group.IsSolvable ↥H := hred.isSolvable S
  have hH's : Group.IsSolvable ↥(H.subgroupOf (mcOf T)) :=
    Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hHG).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hHG).symm.surjective
  exact Group.isSolvable_of_surjective (f := (qPi (mcOf T)).subgroupMap (H.subgroupOf (mcOf T)))
    ((qPi (mcOf T)).subgroupMap_surjective _)

theorem q_mem_pCoreOf_of_mem (S : Setting146 G T M) (hred : IsRedCE T M H PQ p)
    {Uh : Subgroup (OTwoQuot (mcOf T))} (hU2 : IsPGroup 2 Uh)
    (hUn : ∀ x ∈ imageOTwoQuot (mcOf T) H,
      x ∈ Subgroup.normalizer (Uh : Set (OTwoQuot (mcOf T))))
    {t : G} (htT : t ∈ T) (htG : t ∈ mcOf T) (hU : qPi (mcOf T) ⟨t, htG⟩ ∈ Uh) :
    t ∈ pCoreOf 2 H := by
  classical
  have hHG : H ≤ mcOf T := S.le_mcOf hred.isHTM
  have hker2 : IsPGroup 2 (qPi (mcOf T)).ker := by
    unfold qPi
    rw [QuotientGroup.ker_mk']
    exact CFSG.LieType.BorelTits.pCore_isPGroup 2
  have hcomap : IsPGroup 2 ↥(Uh.comap (qPi (mcOf T))) := hU2.comap_of_ker_isPGroup _ hker2
  let W : Subgroup G := (Uh.comap (qPi (mcOf T))).map (mcOf T).subtype
  have hW2 : IsPGroup 2 ↥W :=
    hcomap.of_equiv ((Uh.comap (qPi (mcOf T))).equivMapOfInjective (mcOf T).subtype
      (mcOf T).subtype_injective)
  have hmemW : ∀ y : G, y ∈ W ↔ ∃ hy : y ∈ mcOf T, qPi (mcOf T) ⟨y, hy⟩ ∈ Uh := by
    intro y
    constructor
    · rintro ⟨y', hy', rfl⟩
      exact ⟨y'.2, hy'⟩
    · rintro ⟨hy, hyU⟩
      exact ⟨⟨y, hy⟩, hyU, rfl⟩
  have hHn : ∀ h ∈ H, ∀ y : G, y ∈ W → h * y * h⁻¹ ∈ W := by
    intro h hh y hy
    obtain ⟨hyG, hyU⟩ := (hmemW y).mp hy
    have hhG : h ∈ mcOf T := hHG hh
    refine (hmemW _).mpr ⟨(mcOf T).mul_mem ((mcOf T).mul_mem hhG hyG) ((mcOf T).inv_mem hhG), ?_⟩
    have hx : qPi (mcOf T) ⟨h, hhG⟩ ∈ imageOTwoQuot (mcOf T) H :=
      ⟨_, Subgroup.mem_subgroupOf.mpr hh, rfl⟩
    have := (Subgroup.mem_normalizer_iff.mp (hUn _ hx) _).mp hyU
    have e : qPi (mcOf T) ⟨h * y * h⁻¹,
        (mcOf T).mul_mem ((mcOf T).mul_mem hhG hyG) ((mcOf T).inv_mem hhG)⟩ =
        qPi (mcOf T) ⟨h, hhG⟩ * qPi (mcOf T) ⟨y, hyG⟩ * (qPi (mcOf T) ⟨h, hhG⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e]
    exact this
  have hnorm : H ≤ Subgroup.normalizer ((H ⊓ W : Subgroup G) : Set G) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨hyH, hyW⟩
      exact ⟨H.mul_mem (H.mul_mem hh hyH) (H.inv_mem hh), hHn h hh y hyW⟩
    · rintro ⟨hyH, hyW⟩
      refine ⟨?_, ?_⟩
      · have := H.mul_mem (H.mul_mem (H.inv_mem hh) hyH) hh
        simpa [mul_assoc] using this
      · have := hHn h⁻¹ (H.inv_mem hh) _ hyW
        simpa [mul_assoc] using this
  have hle : H ⊓ W ≤ pCoreOf 2 H :=
    le_pCoreOf_of_le_normalizer 2 inf_le_left hnorm (hW2.to_le inf_le_right)
  exact hle ⟨hred.isHTM.1.1 htT, (hmemW t).mpr ⟨htG, hU⟩⟩

theorem q_relIndex_le_index (S : Setting146 G T M) (hred : IsRedCE T M H PQ p)
    {N : Subgroup (OTwoQuot (mcOf T))} [N.Normal]
    (hN : ∀ (t : G) (ht : t ∈ mcOf T), t ∈ T → qPi (mcOf T) ⟨t, ht⟩ ∈ N → t ∈ pCoreOf 2 H) :
    (pCoreOf 2 H).relIndex T ≤ N.index := by
  classical
  have hTG : T ≤ mcOf T := hred.isHTM.1.1.trans (S.le_mcOf hred.isHTM)
  let lam : ↥T →* OTwoQuot (mcOf T) ⧸ N :=
    (QuotientGroup.mk' N).comp ((qPi (mcOf T)).comp (Subgroup.inclusion hTG))
  have hker : lam.ker ≤ (pCoreOf 2 H).subgroupOf T := by
    intro x hx
    have hx' : (QuotientGroup.mk (qPi (mcOf T) (Subgroup.inclusion hTG x)) :
        OTwoQuot (mcOf T) ⧸ N) = 1 := MonoidHom.mem_ker.mp hx
    have := (QuotientGroup.eq_one_iff _).mp hx'
    exact Subgroup.mem_subgroupOf.mpr (hN x (hTG x.2) x.2 this)
  have h1 : ((pCoreOf 2 H).subgroupOf T).index ∣ lam.ker.index := Subgroup.index_dvd_of_le hker
  have h2 : lam.ker.index = Nat.card lam.range := Subgroup.index_ker lam
  have h3 : Nat.card lam.range ≤ Nat.card (OTwoQuot (mcOf T) ⧸ N) :=
    Nat.card_le_card_of_injective _ Subtype.val_injective
  have h4 : Nat.card (OTwoQuot (mcOf T) ⧸ N) = N.index := (Subgroup.index_eq_card N).symm
  have h5 : 0 < lam.ker.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have := Nat.le_of_dvd h5 h1
  show ((pCoreOf 2 H).subgroupOf T).index ≤ N.index
  omega

end Setting

section MDet

variable {G : Type} [Group G] [Finite G] {T M H PQ : Subgroup G} {p : ℕ}

theorem q_prime_dvd_of_solvable_hat (S : Setting146 G T M) (hred : IsRedCE T M H PQ p)
    (hmax : PMaximal T M p) {Hp : Subgroup (OTwoQuot (mcOf T))}
    (hHp : imageOTwoQuot (mcOf T) H ≤ Hp) (hs : Group.IsSolvable ↥Hp) {r : ℕ} (hr : r.Prime)
    (hd : r ∣ Nat.card Hp) : r = 2 ∨ r = 3 ∨ (p = 5 ∧ r = 5) := by
  classical
  have hHG : H ≤ mcOf T := S.le_mcOf hred.isHTM
  have hRp : IsPGroup 2 (CFSG.Open.pCore 2 ↥(mcOf T)) := CFSG.LieType.BorelTits.pCore_isPGroup 2
  let Hq : Subgroup G := (Hp.comap (qPi (mcOf T))).map (mcOf T).subtype
  have hHqs : Group.IsSolvable ↥Hq := by
    have h1 : Group.IsSolvable ↥(Hp.comap (qPi (mcOf T))) :=
      isSolvable_comap_quotient _ hRp hs
    exact Group.isSolvable_of_surjective
      (f := ((Hp.comap (qPi (mcOf T))).equivMapOfInjective (mcOf T).subtype
        (mcOf T).subtype_injective).toMonoidHom)
      ((Hp.comap (qPi (mcOf T))).equivMapOfInjective (mcOf T).subtype
        (mcOf T).subtype_injective).surjective
  have hHHq : H ≤ Hq := by
    intro h hh
    exact ⟨⟨h, hHG hh⟩, hHp ⟨_, Subgroup.mem_subgroupOf.mpr hh, rfl⟩, rfl⟩
  have hHqM : Hq ≤ mcOf T := Subgroup.map_subtype_le _
  have hdvd : r ∣ Nat.card ↥Hq := by
    have h1 : Nat.card Hp ∣ Nat.card ↥(Hp.comap (qPi (mcOf T))) := card_dvd_comap_quotient _ Hp
    have h2 : Nat.card ↥(Hp.comap (qPi (mcOf T))) = Nat.card ↥Hq :=
      Nat.card_congr ((Hp.comap (qPi (mcOf T))).equivMapOfInjective (mcOf T).subtype
        (mcOf T).subtype_injective).toEquiv
    rw [← h2]
    exact hd.trans h1
  have hsolv := input14614Solv_proved G T M S H PQ p hred hmax Hq hHHq hHqM hHqs
  rcases S.p_eq_three_or_five_of_isRedCE hred with hp | hp
  · rcases hsolv.1 hp r hr hdvd with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rcases hsolv.2 hp r hr hdvd with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨hp, h⟩)

end MDet

section Borel

variable {G : Type} [Group G] [Finite G] {T M H PQ : Subgroup G} {p : ℕ}

theorem q_odd_of_dvd_pred {F : Type} [Field F] [Finite F] [CharP F 2] {r : ℕ} (hr : r.Prime)
    (hd : r ∣ Nat.card F - 1) : r ≠ 2 := by
  rintro rfl
  obtain ⟨n, hn, hcard⟩ := SL2Sylow.exists_card_eq_two_pow (F := F)
  rw [hcard] at hd
  have h1 : 2 ∣ 2 ^ n := dvd_pow_self 2 hn.ne'
  have h2 := Nat.dvd_sub h1 hd
  have h3 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  rw [Nat.sub_sub_self h3] at h2
  omega

theorem q_prime_dvd_pred (S : Setting146 G T M) (hred : IsRedCE T M H PQ p) (hmax : PMaximal T M p)
    {N₁ N₂ : Subgroup (OTwoQuot (mcOf T))} {ŝ : OTwoQuot (mcOf T)} (hF : CaseIFacts N₁ N₂ ŝ)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hq : 4 ≤ Nat.card F)
    (e : ↥N₁ ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hKle : imageOTwoQuot (mcOf T) (oTwoUpper H) ≤ N₁ ⊔ N₂) {r : ℕ} (hr : r.Prime)
    (hd : r ∣ Nat.card F - 1) : r = 3 ∨ (p = 5 ∧ r = 5) := by
  classical
  have hSyl := q_hatT_sylow S
  have hSyl₁ := q_isSylowTwoOf_inf_fst hF hSyl
  have hSyl₂ := q_isSylowTwoOf_inf_snd hF hSyl
  let e₂ : ↥N₂ ≃* Matrix.SpecialLinearGroup (Fin 2) F := (q_equiv_snd hF).trans e
  have hP₁ : ∀ A : Subgroup (OTwoQuot (mcOf T)), A ≤ N₁ →
      imageOTwoQuot (mcOf T) T ⊓ N₁ ≤ A → Group.IsSolvable ↥A →
      A ≤ Subgroup.normalizer ((imageOTwoQuot (mcOf T) T ⊓ N₁ : Subgroup _) : Set _) :=
    fun A hAN hUA hAs => sl2_le_normalizer_of_solvable_ambient hq e inf_le_right hAN
      hSyl₁.2.1 hSyl₁.2.2 hUA hAs
  have hP₂ : ∀ A : Subgroup (OTwoQuot (mcOf T)), A ≤ N₂ →
      imageOTwoQuot (mcOf T) T ⊓ N₂ ≤ A → Group.IsSolvable ↥A →
      A ≤ Subgroup.normalizer ((imageOTwoQuot (mcOf T) T ⊓ N₂ : Subgroup _) : Set _) :=
    fun A hAN hUA hAs => sl2_le_normalizer_of_solvable_ambient hq e₂ inf_le_right hAN
      hSyl₂.2.1 hSyl₂.2.2 hUA hAs
  have hHnorm := q_hat_normalizes_U hF hSyl (q_hatT_le_hatH hred)
    (q_image_mono (oTwoUpper_le H)) hKle (q_hatH_solvable S hred)
    (fun x hx => q_hat_decomp S hred hx) hP₁ hP₂
  have hEq := q_inf_sup_eq hF hSyl
  have hB₁ := sl2_normalizer_inf_solvable_dvd e inf_le_right hSyl₁.2.1 hSyl₁.2.2
  have hB₂ := sl2_normalizer_inf_solvable_dvd e₂ inf_le_right hSyl₂.2.1 hSyl₂.2.2
  have hBs := q_two_closed_prod_normalizer_solvable N₁ N₂ hF.comm hF.disj
    (imageOTwoQuot (mcOf T) T ⊓ N₁) (imageOTwoQuot (mcOf T) T ⊓ N₂) inf_le_right inf_le_right
    hB₁.1 hB₂.1
  have hBc := q_two_closed_prod_normalizer_card N₁ N₂ hF.comm hF.disj
    (imageOTwoQuot (mcOf T) T ⊓ N₁) (imageOTwoQuot (mcOf T) T ⊓ N₂) inf_le_right inf_le_right
  set Uh : Subgroup (OTwoQuot (mcOf T)) :=
    (imageOTwoQuot (mcOf T) T ⊓ N₁) ⊔ (imageOTwoQuot (mcOf T) T ⊓ N₂) with hUh
  have hHB : imageOTwoQuot (mcOf T) H ≤ Subgroup.normalizer
      ((Subgroup.normalizer (Uh : Set (OTwoQuot (mcOf T))) ⊓ (N₁ ⊔ N₂) : Subgroup _) : Set _) := by
    intro x hx
    have h1 : x ∈ Subgroup.normalizer (Uh : Set (OTwoQuot (mcOf T))) := by
      rw [← hEq]
      exact hHnorm x hx
    have h2 : x ∈ Subgroup.normalizer ((N₁ ⊔ N₂ : Subgroup (OTwoQuot (mcOf T))) : Set _) :=
      (Subgroup.normalizer_eq_top_iff.mpr hF.normal) ▸ Subgroup.mem_top x
    exact q_mem_normalizer_inf (Subgroup.le_normalizer h1) h2
  have hsup : Group.IsSolvable ↥(imageOTwoQuot (mcOf T) H ⊔
      (Subgroup.normalizer (Uh : Set (OTwoQuot (mcOf T))) ⊓ (N₁ ⊔ N₂))) :=
    isSolvable_sup_of_normalizes hHB (q_hatH_solvable S hred) hBs
  have hdvd : r ∣ Nat.card ↥(imageOTwoQuot (mcOf T) H ⊔
      (Subgroup.normalizer (Uh : Set (OTwoQuot (mcOf T))) ⊓ (N₁ ⊔ N₂))) := by
    have h1 : Nat.card F - 1 ∣ Nat.card ↥(Subgroup.normalizer (Uh : Set (OTwoQuot (mcOf T))) ⊓
        (N₁ ⊔ N₂)) := hBc ▸ hB₁.2.trans (dvd_mul_right _ _)
    exact hd.trans (h1.trans (Subgroup.card_dvd_of_le le_sup_right))
  rcases q_prime_dvd_of_solvable_hat S hred hmax le_sup_left hsup hr hdvd with h | h | h
  · exact absurd h (q_odd_of_dvd_pred hr hd)
  · exact Or.inl h
  · exact Or.inr h

end Borel

section Eight

variable {G : Type} [Group G] [Finite G] {T M H PQ : Subgroup G}

theorem q_factorization_two_mul (n a : ℕ) (hn : ¬ 2 ∣ n) :
    (n * 2 ^ a).factorization 2 = a := by
  have hn0 : n ≠ 0 := fun h => hn (h ▸ dvd_zero 2)
  rw [Nat.factorization_mul hn0 (pow_ne_zero a two_ne_zero), Nat.factorization_pow]
  simp [Nat.factorization_eq_zero_of_not_dvd hn, Nat.Prime.factorization_self Nat.prime_two]

end Eight

section Wreath

variable {G : Type} [Group G] [Finite G] {T M H PQ : Subgroup G} {p : ℕ}

omit [Finite G] in
theorem q_hatK_le {K₁ : Subgroup G} {s : G} (hK₁ : K₁ ∈ cComp (mcOf T)) (hsG : s ∈ mcOf T)
    (hKz : conjClosure (oTwoUpper H) (mcOf T) = K₁ ⊔ conjSub s K₁) :
    imageOTwoQuot (mcOf T) (oTwoUpper H) ≤
      imageOTwoQuot (mcOf T) K₁ ⊔ imageOTwoQuot (mcOf T) (conjSub s K₁) := by
  have hK₁G : K₁ ≤ mcOf T := le_of_mem_cComp hK₁
  have hK₂G : conjSub s K₁ ≤ mcOf T := le_of_mem_cComp (conjSub_mem_cComp_of_mem hK₁ hsG)
  calc imageOTwoQuot (mcOf T) (oTwoUpper H)
      ≤ imageOTwoQuot (mcOf T) (K₁ ⊔ conjSub s K₁) :=
        q_image_mono (hKz ▸ le_conjClosure _ _)
    _ = _ := q_image_sup hK₁G hK₂G

theorem q_hat_normalizes_U_sl2 (S : Setting146 G T M) (hred : IsRedCE T M H PQ p)
    {N₁ N₂ : Subgroup (OTwoQuot (mcOf T))} {ŝ : OTwoQuot (mcOf T)} (hF : CaseIFacts N₁ N₂ ŝ)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hq : 4 ≤ Nat.card F)
    (e : ↥N₁ ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hKle : imageOTwoQuot (mcOf T) (oTwoUpper H) ≤ N₁ ⊔ N₂) :
    ∀ x ∈ imageOTwoQuot (mcOf T) H, x ∈ Subgroup.normalizer
      ((imageOTwoQuot (mcOf T) T ⊓ (N₁ ⊔ N₂) : Subgroup _) : Set (OTwoQuot (mcOf T))) := by
  have hSyl := q_hatT_sylow S
  have hSyl₁ := q_isSylowTwoOf_inf_fst hF hSyl
  have hSyl₂ := q_isSylowTwoOf_inf_snd hF hSyl
  let e₂ : ↥N₂ ≃* Matrix.SpecialLinearGroup (Fin 2) F := (q_equiv_snd hF).trans e
  exact q_hat_normalizes_U hF hSyl (q_hatT_le_hatH hred) (q_image_mono (oTwoUpper_le H)) hKle
    (q_hatH_solvable S hred) (fun x hx => q_hat_decomp S hred hx)
    (fun A hAN hUA hAs => sl2_le_normalizer_of_solvable_ambient hq e inf_le_right hAN
      hSyl₁.2.1 hSyl₁.2.2 hUA hAs)
    (fun A hAN hUA hAs => sl2_le_normalizer_of_solvable_ambient hq e₂ inf_le_right hAN
      hSyl₂.2.1 hSyl₂.2.2 hUA hAs)

theorem q_relIndex_le_index_sl2 (S : Setting146 G T M) (hred : IsRedCE T M H PQ p)
    {N₁ N₂ : Subgroup (OTwoQuot (mcOf T))} {ŝ : OTwoQuot (mcOf T)} (hF : CaseIFacts N₁ N₂ ŝ)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hq : 4 ≤ Nat.card F)
    (e : ↥N₁ ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hKle : imageOTwoQuot (mcOf T) (oTwoUpper H) ≤ N₁ ⊔ N₂) :
    (pCoreOf 2 H).relIndex T ≤ (N₁ ⊔ N₂).index := by
  have hNn := hF.normal
  have hSyl := q_hatT_sylow S
  refine q_relIndex_le_index S hred (N := N₁ ⊔ N₂) fun t ht htT hN => ?_
  refine q_mem_pCoreOf_of_mem S hred (Uh := imageOTwoQuot (mcOf T) T ⊓ (N₁ ⊔ N₂))
    (hSyl.2.1.to_inf_left) (q_hat_normalizes_U_sl2 S hred hF hq e hKle) htT ht ?_
  exact ⟨⟨_, Subgroup.mem_subgroupOf.mpr htT, rfl⟩, hN⟩

end Wreath

section EightMain

variable {G : Type} [Group G] [Finite G] {T M H PQ : Subgroup G}

theorem q_relIndex_eq_eight (h12 : Stage14612PartP) (S : Setting146 G T M)
    (hred : IsRedCE T M H PQ 3) (hmax : PMaximal T M 3) :
    (pCoreOf 2 H).relIndex T = 8 := by
  classical
  obtain ⟨-, H₀, H₁, H₂, t, hdec⟩ := h12 G T M S H PQ 3 hred hmax
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH : T ≤ H := hred.isHTM.1.1
  have hQT : pCoreOf 2 H ≤ T := S.pCoreOf_le_T hred.isHTM
  obtain ⟨b, hb⟩ := (IsPGroup.iff_card (p := 2)).mp (pCoreOf_isPGroup 2 H)
  have h1 := hdec.card_H₀
  have h2 := hdec.relIndex_eq_two_of_p_three S hred
  have h3 := Subgroup.relIndex_mul_card H₀ H
  rw [inf_eq_left.mpr hdec.le, h2, h1, hb] at h3
  have hHcard : Nat.card H = 9 * 2 ^ (b + 3) := by rw [← h3]; ring
  have hSyl : IsSylowTwoOf T H := isSylowTwoOf_of_le151 S.hyp.sylow hTH
  have hT := q_card_of_isSylowTwoOf hSyl
  rw [hHcard, q_factorization_two_mul 9 (b + 3) (by norm_num)] at hT
  have h4 := Subgroup.relIndex_mul_card (pCoreOf 2 H) T
  rw [inf_eq_left.mpr hQT, hT, hb] at h4
  have hpos : 0 < 2 ^ b := pow_pos two_pos b
  have : (pCoreOf 2 H).relIndex T * 2 ^ b = 8 * 2 ^ b := by rw [h4]; ring
  exact Nat.eq_of_mul_eq_mul_right hpos this

end EightMain

section Final

variable {G : Type} [Group G] [Finite G] {T M H PQ : Subgroup G} {p : ℕ}

theorem q_sl2_setup (h36 : A36ForSQTK) (hlist : SQTKList3Dvd) (iS : Input14614NoSz)
    (S : Setting146 G T M) (hred : IsRedCE T M H PQ p) (hmax : PMaximal T M p)
    {K₁ : Subgroup G} {s : G} (hK₁ : K₁ ∈ cComp (mcOf T)) (hsT : s ∈ T)
    (hsN : s ∉ Subgroup.normalizer (K₁ : Set G))
    (hKz : conjClosure (oTwoUpper H) (mcOf T) = K₁ ⊔ conjSub s K₁)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hq : 4 ≤ Nat.card F) (hpF : p ∣ Nat.card F - 1)
    (e : Nonempty (OTwoQuot K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) F)) :
    ∃ hsG : s ∈ mcOf T, Nonempty (Matrix.SpecialLinearGroup (Fin 2) F ≃*
        ↥(imageOTwoQuot (mcOf T) K₁)) ∧
      CaseIFacts (imageOTwoQuot (mcOf T) K₁) (imageOTwoQuot (mcOf T) (conjSub s K₁))
        (qPi (mcOf T) ⟨s, hsG⟩) := by
  classical
  obtain ⟨e⟩ := e
  have hTG : T ≤ mcOf T := hred.isHTM.1.1.trans (S.le_mcOf hred.isHTM)
  have hsG : s ∈ mcOf T := hTG hsT
  obtain ⟨eK⟩ := q_oTwoQuot_equiv_image (subnormal_of_mem_cComp hK₁)
  let e1 : Matrix.SpecialLinearGroup (Fin 2) F ≃* ↥(imageOTwoQuot (mcOf T) K₁) := e.symm.trans eK
  have hs : IsSimpleGroup ↥(imageOTwoQuot (mcOf T) K₁) :=
    haveI := q_isSimpleGroup_sl2 hq
    e1.symm.isSimpleGroup
  have hnc : ∃ a b : ↥(imageOTwoQuot (mcOf T) K₁), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := q_nonabelian_sl2 hq
    exact ⟨e1 a, e1 b, fun h => hab (e1.injective (by simpa using h))⟩
  obtain ⟨n, hn, hcardF⟩ := SL2Sylow.exists_card_eq_two_pow (F := F)
  have hcard : Nat.card ↥(imageOTwoQuot (mcOf T) K₁) =
      Nat.card F * (Nat.card F ^ 2 - 1) := by
    rw [← Nat.card_congr e1.toEquiv]
    exact CFSG.GorensteinWalter.sl2_card_formula F
  have hpF2 : Nat.card F - 1 ∣ Nat.card F ^ 2 - 1 := by
    have := Nat.sub_dvd_pow_sub_pow (Nat.card F) 1 2
    simpa using this
  have h3 : 3 ∣ Nat.card ↥(imageOTwoQuot (mcOf T) K₁) := by
    rw [hcard]
    refine Dvd.dvd.mul_left ?_ _
    have h4 := Nat.sub_dvd_pow_sub_pow 4 1 n
    have h5 : Nat.card F ^ 2 = 4 ^ n := by rw [hcardF, ← pow_mul, mul_comm, pow_mul]; norm_num
    rw [h5]
    simpa using h4
  have hp : p ∣ Nat.card ↥(imageOTwoQuot (mcOf T) K₁) := by
    rw [hcard]
    exact Dvd.dvd.mul_left (hpF.trans hpF2) _
  exact ⟨hsG, ⟨e1⟩, q_caseI_facts h36 hlist iS S hred hmax hK₁ hsG hsN hKz hs hnc h3 hp⟩

theorem q_wreath_SL2 (h36 : A36ForSQTK) (hlist : SQTKList3Dvd) (iS : Input14614NoSz)
    (S : Setting146 G T M) (hred : IsRedCE T M H PQ p) (hmax : PMaximal T M p)
    {K₁ : Subgroup G} {s : G} (hK₁ : K₁ ∈ cComp (mcOf T)) (hsT : s ∈ T)
    (hsN : s ∉ Subgroup.normalizer (K₁ : Set G))
    (hKz : conjClosure (oTwoUpper H) (mcOf T) = K₁ ⊔ conjSub s K₁)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hq : 4 ≤ Nat.card F) (hpF : p ∣ Nat.card F - 1)
    (e : Nonempty (OTwoQuot K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) F))
    (hrel : 2 * Nat.card (MulAut (Matrix.SpecialLinearGroup (Fin 2) F)) ^ 2 ≤
      (pCoreOf 2 H).relIndex T * Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) ^ 2) :
    Nonempty (OTwoQuot (mcOf T) ≃*
      (MulAut (Matrix.SpecialLinearGroup (Fin 2) F) ≀ᵣ Multiplicative (ZMod 2))) := by
  classical
  obtain ⟨hsG, ⟨e1⟩, hF⟩ := q_sl2_setup h36 hlist iS S hred hmax hK₁ hsT hsN hKz hq hpF e
  have hKle := q_hatK_le hK₁ hsG hKz
  have hrelle := q_relIndex_le_index_sl2 S hred hF hq e1.symm hKle
  have hcardX : Nat.card ↥(imageOTwoQuot (mcOf T) K₁) ^ 2 * (pCoreOf 2 H).relIndex T ≤
      Nat.card (OTwoQuot (mcOf T)) := by
    have h1 := Subgroup.index_mul_card (imageOTwoQuot (mcOf T) K₁ ⊔
      imageOTwoQuot (mcOf T) (conjSub s K₁))
    rw [q_card_sup_pair hF] at h1
    rw [← h1, mul_comm]
    exact Nat.mul_le_mul hrelle (le_refl _)
  have hcardW : 2 * Nat.card (MulAut (Matrix.SpecialLinearGroup (Fin 2) F)) ^ 2 ≤
      Nat.card (OTwoQuot (mcOf T)) := by
    have h1 : Nat.card ↥(imageOTwoQuot (mcOf T) K₁) =
        Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) := (Nat.card_congr e1.toEquiv).symm
    rw [h1] at hcardX
    calc _ ≤ (pCoreOf 2 H).relIndex T * Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) ^ 2 := hrel
      _ = _ := by ring
      _ ≤ _ := hcardX
  exact q_mulEquiv_wreath_mulAut _ _ (qPi (mcOf T) ⟨s, hsG⟩) e1 hF.conj hF.comm hF.disj hF.perm
    hF.normal hF.cen hF.centreless hcardW

end Final

end CFSG.Quasithin
