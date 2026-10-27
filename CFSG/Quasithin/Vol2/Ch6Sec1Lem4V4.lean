module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34FiveDefs
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4V2
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4VIn

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

section

variable {Γ G : Type*} [Group Γ] [Group G]

theorem exists_five_overgroup614 [Finite Γ] [Finite G] {M X P T D : Subgroup Γ} {N : Subgroup G}
    (σ : ↥M →* G) (hXM : X ≤ M) (hTM : T ≤ M) (hDT : D ≤ T) (hPX : P ≤ X) (hPT : P ≤ T)
    (hT2 : IsPGroup 2 T) (hPn : (P.subgroupOf X).Normal) (hX5 : P.relIndex X = 5)
    (hXO : X = oTwoUpper X) (hTX : T ≤ Subgroup.normalizer (X : Set Γ))
    (hXN : ∀ x (hx : x ∈ X), σ ⟨x, hXM hx⟩ ∈ N) (hX1 : ∃ x, ∃ hx : x ∈ X, σ ⟨x, hXM hx⟩ ≠ 1)
    (hDs : IsSylowTwoOf ((D.subgroupOf M).map σ) N) :
    ((D.subgroupOf M).map σ).relIndex ((X.subgroupOf M).map σ ⊔ (D.subgroupOf M).map σ) = 5 ∧
      (X.subgroupOf M).map σ ⊔ (D.subgroupOf M).map σ ≤ N := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set τ : ↥X →* G := σ.comp (Subgroup.inclusion hXM) with hτ
  set X' := (X.subgroupOf M).map σ with hX'
  have hX'τ : X' = τ.range := by
    ext g
    constructor
    · rintro ⟨⟨x, hxM⟩, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨⟨x, hx⟩, rfl⟩
      exact ⟨⟨x, hXM hx⟩, hx, rfl⟩
  set D' := (D.subgroupOf M).map σ with hD'
  set T' := (T.subgroupOf M).map σ with hT'
  set P' := (P.subgroupOf X).map τ with hP'
  have hP2 : IsPGroup 2 P := hT2.to_le hPT
  have hP'2 : IsPGroup 2 P' := (hP2.of_equiv (Subgroup.subgroupOfEquivOfLe hPX).symm).map τ
  have hP'X' : P' ≤ X' := hX'τ ▸ Subgroup.map_le_range _ _
  have hX'N : X' ≤ N := by
    rintro _ ⟨⟨x, hxM⟩, hx, rfl⟩
    exact hXN x hx
  have hX'O : X' = oTwoUpper X' := by
    have h1 : oTwoUpper (⊤ : Subgroup ↥X) = ⊤ := by
      apply Subgroup.map_injective X.subtype_injective
      rw [← oTwoUpper_map, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
      exact hXO.symm
    rw [hX'τ, MonoidHom.range_eq_map, oTwoUpper_map, h1]
  set ρ := τ.rangeRestrict with hρ
  have hsub : P'.subgroupOf τ.range = (P.subgroupOf X).map ρ := by
    ext ⟨φ, hφ⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map, Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, he⟩
      exact ⟨x, hx, Subtype.ext he⟩
    · rintro ⟨x, hx, he⟩
      exact ⟨x, hx, congrArg Subtype.val he⟩
  have hdvd : P'.relIndex X' ∣ 5 := by
    rw [hX'τ]
    show (P'.subgroupOf τ.range).index ∣ 5
    rw [hsub, ← hX5]
    exact Subgroup.index_map_dvd _ (MonoidHom.rangeRestrict_surjective τ)
  have hX5' : P'.relIndex X' = 5 := by
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hdvd with h | h
    · exfalso
      rw [Subgroup.relIndex_eq_one] at h
      obtain ⟨x, hx, hx1⟩ := hX1
      have hbot : X' = ⊥ := by
        rw [hX'O, eq_bot_iff, oTwoUpper, Subgroup.closure_le]
        rintro g ⟨hg, hgo⟩
        obtain ⟨k, hk⟩ := hP'2 ⟨g, h hg⟩
        have hk' : g ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
        exact Subgroup.mem_bot.mpr (eq_one_of_pow_two_of_odd614 hk' (pow_orderOf_eq_one g) hgo)
      have hmem : σ ⟨x, hXM hx⟩ ∈ X' := ⟨⟨x, hXM hx⟩, hx, rfl⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hx1 hmem
    · exact h
  have hT'2 : IsPGroup 2 T' := (hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTM).symm).map σ
  have hD'T' : D' ≤ T' := Subgroup.map_mono fun x hx => hDT hx
  have hR : T' ⊓ N ≤ D' := by
    have hDR : D' ≤ T' ⊓ N := le_inf hD'T' hDs.1
    have h := Subgroup.relIndex_mul_relIndex D' (T' ⊓ N) N hDR inf_le_right
    have hR2 : IsPGroup 2 ↥(T' ⊓ N) := hT'2.to_le inf_le_left
    obtain ⟨n, hn⟩ := hR2.exists_card_eq
    have hdv : D'.relIndex (T' ⊓ N) ∣ 2 ^ n := hn ▸ Subgroup.index_dvd_card _
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdv
    rcases k with _ | k
    · rw [pow_zero, Subgroup.relIndex_eq_one] at hk
      exact hk
    · exfalso
      apply hDs.2.2
      show 2 ∣ D'.relIndex N
      rw [← h, hk, pow_succ]
      exact dvd_mul_of_dvd_left (dvd_mul_left 2 _) _
  have hP'T' : P' ≤ T' := by
    rintro _ ⟨⟨p, hpX⟩, hp, rfl⟩
    exact ⟨⟨p, hTM (hPT hp)⟩, hPT hp, rfl⟩
  have hP'D' : P' ≤ D' := le_trans (le_inf hP'T' (hP'X'.trans hX'N)) hR
  have hT'X' : T' ≤ Subgroup.normalizer (X' : Set G) := by
    have h1 : T.subgroupOf M ≤ Subgroup.normalizer ((X.subgroupOf M : Subgroup ↥M) : Set ↥M) := by
      intro t ht
      rw [Subgroup.mem_normalizer_iff]
      intro h
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact Subgroup.mem_normalizer_iff.mp (hTX ht) h
    exact le_trans (Subgroup.map_mono h1) (Subgroup.le_normalizer_map σ)
  have hinf : D' ⊓ X' = P' := by
    refine le_antisymm ?_ (le_inf hP'D' hP'X')
    rintro g ⟨hgD, hgX⟩
    have hgX' : g ∈ τ.range := hX'τ ▸ hgX
    have hPn' : (P'.subgroupOf τ.range).Normal := by
      rw [hsub]
      exact hPn.map _ (MonoidHom.rangeRestrict_surjective τ)
    set q : ↥τ.range ⧸ P'.subgroupOf τ.range := QuotientGroup.mk ⟨g, hgX'⟩ with hq
    have hcardQ : Nat.card (↥τ.range ⧸ P'.subgroupOf τ.range) = 5 := by
      have : P'.relIndex τ.range = 5 := hX'τ ▸ hX5'
      exact this
    have hq5 : q ^ 5 = 1 := by
      rw [← hcardQ]
      exact pow_card_eq_one'
    obtain ⟨k, hk⟩ := (hDs.2.1) ⟨g, hgD⟩
    have hk' : g ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hqk : q ^ 2 ^ k = 1 := by
      rw [hq, ← QuotientGroup.mk_pow]
      have : (⟨g, hgX'⟩ : ↥τ.range) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk')
      rw [this, QuotientGroup.mk_one]
    have hq1 := eq_one_of_pow_two_of_odd614 hqk hq5 (by decide)
    rw [hq, QuotientGroup.eq_one_iff] at hq1
    exact hq1
  have hrel := CFSG.Quasithin.B6.relIndex_inf_eq_relIndex_sup (hT'X'.trans' hD'T')
  rw [hinf, hX5', sup_comm] at hrel
  exact ⟨hrel.symm, sup_le hX'N hDs.1⟩

end

section

variable {Γ : Type} [Group Γ]

@[expose] noncomputable def rho614 (K : Subgroup Γ) :
    ↥(Subgroup.normalizer (K : Set Γ)) →* MulAut (ModO2 K ⧸ Subgroup.center (ModO2 K)) :=
  (quotCenterAut614 (ModO2 K)).comp (actModO2_614 K)

theorem rho614_of_mem (K : Subgroup Γ) {k : Γ} (hk : k ∈ K) :
    rho614 K ⟨k, Subgroup.le_normalizer hk⟩ =
      MulAut.conj ((((⟨k, hk⟩ : ↥K) : ModO2 K)) : ModO2 K ⧸ Subgroup.center (ModO2 K)) := by
  show quotCenterAut614 (ModO2 K) (actModO2_614 K ⟨k, Subgroup.le_normalizer hk⟩) = _
  rw [actModO2_614_of_mem K hk, quotCenterAut614_conj]

theorem centralizerMod_le_normalizer614 (H K : Subgroup Γ) :
    centralizerMod (pCoreOf 2 K) H K ≤ Subgroup.normalizer (K : Set Γ) := by
  have key : ∀ c ∈ centralizerMod (pCoreOf 2 K) H K, ∀ u ∈ K, c * u * c⁻¹ ∈ K := by
    intro c hc u hu
    have h1 := CFSG.LieType.BorelTits.pCoreOf_le 2 K (hc.2.2 u hu)
    have e : c * u * c⁻¹ = (c * u * c⁻¹ * u⁻¹) * u := by group
    rw [e]
    exact K.mul_mem h1 hu
  intro c hc
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨key c hc h, fun hh => ?_⟩
  have := key c⁻¹ (Subgroup.inv_mem _ hc) _ hh
  simpa [mul_assoc] using this

theorem rho614_eq_one_of_mem [Finite Γ] {H K : Subgroup Γ} {c : Γ}
    (hc : c ∈ centralizerMod (pCoreOf 2 K) H K) :
    rho614 K ⟨c, centralizerMod_le_normalizer614 H K hc⟩ = 1 := by
  show quotCenterAut614 (ModO2 K) (actModO2_614 K ⟨c, centralizerMod_le_normalizer614 H K hc⟩) = 1
  rw [actModO2_614_eq_one K fun u hu => hc.2.2 u hu, map_one]

theorem rho614_mem_range [Finite Γ] {H K : Subgroup Γ} {x : Γ}
    (hx : x ∈ K ⊔ centralizerMod (pCoreOf 2 K) H K) (hxN : x ∈ Subgroup.normalizer (K : Set Γ)) :
    rho614 K ⟨x, hxN⟩ ∈ (MulAut.conj : ModO2 K ⧸ Subgroup.center (ModO2 K) →* MulAut _).range := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left K _
    (centralizerMod_le_normalizer614 H K)] at hx
  obtain ⟨k, hk, c, hc, hkc⟩ := hx
  have e : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (K : Set Γ))) =
      ⟨k, Subgroup.le_normalizer hk⟩ * ⟨c, centralizerMod_le_normalizer614 H K hc⟩ :=
    Subtype.ext hkc.symm
  rw [e, map_mul, rho614_eq_one_of_mem hc, mul_one, rho614_of_mem K hk]
  exact ⟨_, rfl⟩

theorem exists_rho614_ne_one {K X : Subgroup Γ} (hXK : X ≤ Subgroup.normalizer (K : Set Γ))
    (hperf : commutator (ModO2 K) = ⊤) (hnt : ¬ ⁅X, K⁆ ≤ pCoreOf 2 K) :
    ∃ x, ∃ hx : x ∈ X, rho614 K ⟨x, hXK hx⟩ ≠ 1 := by
  by_contra hcon
  push Not at hcon
  exact hnt (commutator_le_pCoreOf_of_actModO2_614 hXK fun x hx =>
    eq_one_of_quotCenterAut614_eq_one hperf (hcon x hx))

theorem range_rho614_comp (K : Subgroup Γ) :
    ((rho614 K).comp (Subgroup.inclusion
      (Subgroup.le_normalizer : K ≤ Subgroup.normalizer (K : Set Γ)))).range =
      (MulAut.conj : ModO2 K ⧸ Subgroup.center (ModO2 K) →* MulAut _).range := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨⟨k, hk⟩, rfl⟩
    exact ⟨_, (rho614_of_mem K hk).symm⟩
  · rintro _ ⟨s, rfl⟩
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective s
    obtain ⟨⟨k, hk⟩, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨⟨k, hk⟩, rho614_of_mem K hk⟩

theorem isSylowTwoOf_rho614 {K T : Subgroup Γ} (hT2 : IsPGroup 2 T)
    (hTs : IsSylowTwoOf (T ⊓ K) K) :
    IsSylowTwoOf (((T ⊓ K).subgroupOf (Subgroup.normalizer (K : Set Γ))).map (rho614 K))
      (MulAut.conj : ModO2 K ⧸ Subgroup.center (ModO2 K) →* MulAut _).range := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set τK := (rho614 K).comp (Subgroup.inclusion
    (Subgroup.le_normalizer : K ≤ Subgroup.normalizer (K : Set Γ))) with hτK
  have hD : ((T ⊓ K).subgroupOf (Subgroup.normalizer (K : Set Γ))).map (rho614 K) =
      ((T ⊓ K).subgroupOf K).map τK := by
    ext φ
    constructor
    · rintro ⟨⟨k, hkN⟩, hk, rfl⟩
      exact ⟨⟨k, hk.2⟩, hk, rfl⟩
    · rintro ⟨⟨k, hkK⟩, hk, rfl⟩
      exact ⟨⟨k, Subgroup.le_normalizer hkK⟩, hk, rfl⟩
  rw [hD, ← range_rho614_comp K]
  refine ⟨Subgroup.map_le_range _ _, ?_, ?_⟩
  · exact ((hT2.to_le inf_le_left).of_equiv
      (Subgroup.subgroupOfEquivOfLe (inf_le_right : T ⊓ K ≤ K)).symm).map τK
  · set ρ := τK.rangeRestrict
    have hsub : (((T ⊓ K).subgroupOf K).map τK).subgroupOf τK.range =
        ((T ⊓ K).subgroupOf K).map ρ := by
      ext ⟨φ, hφ⟩
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_map, Subgroup.mem_map]
      constructor
      · rintro ⟨x, hx, he⟩
        exact ⟨x, hx, Subtype.ext he⟩
      · rintro ⟨x, hx, he⟩
        exact ⟨x, hx, congrArg Subtype.val he⟩
    intro h2
    apply hTs.2.2
    have h3 : (((T ⊓ K).subgroupOf K).map τK).relIndex τK.range ∣ (T ⊓ K).relIndex K := by
      show ((((T ⊓ K).subgroupOf K).map τK).subgroupOf τK.range).index ∣
        ((T ⊓ K).subgroupOf K).index
      rw [hsub]
      exact Subgroup.index_map_dvd _ (MonoidHom.rangeRestrict_surjective τK)
    exact h2.trans h3

end

section

theorem exists_pullback_inn614 {Y : Type} [Group Y] [Finite Y] (hZ : Subgroup.center Y = ⊥)
    {D Q : Subgroup (MulAut Y)} (hDs : IsSylowTwoOf D (MulAut.conj : Y →* MulAut Y).range)
    (hDQ : D ≤ Q) (hQN : Q ≤ (MulAut.conj : Y →* MulAut Y).range) (h5 : D.relIndex Q = 5) :
    ∃ S P : Subgroup Y, IsSylowTwoOf S ⊤ ∧ S ≤ P ∧ Nat.card P = 5 * Nat.card S ∧
      S.map (MulAut.conj : Y →* MulAut Y) = D ∧ P.map (MulAut.conj : Y →* MulAut Y) = Q := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ι : Y →* MulAut Y := MulAut.conj with hι
  have hinj : Function.Injective ι := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro y hy
    have hyc : y ∈ Subgroup.center Y := by
      rw [Subgroup.mem_center_iff]
      intro z
      have := congrArg (fun φ : MulAut Y => φ z) (MonoidHom.mem_ker.mp hy)
      simp only [hι, MulAut.conj_apply, MulAut.one_apply] at this
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this.symm
    rw [hZ] at hyc
    exact hyc
  set S := D.comap ι with hS
  set P := Q.comap ι with hP
  have hSmap : S.map ι = D := Subgroup.map_comap_eq_self hDs.1
  have hPmap : P.map ι = Q := Subgroup.map_comap_eq_self hQN
  have hSs : IsSylowTwoOf S ⊤ := by
    refine ⟨le_top, hDs.2.1.comap_of_injective ι hinj, ?_⟩
    have h1 : (S.map ι).relIndex ((⊤ : Subgroup Y).map ι) = S.index := by
      rw [Subgroup.relIndex_map_map, (MonoidHom.ker_eq_bot_iff _).mpr hinj, sup_bot_eq,
        sup_bot_eq, Subgroup.relIndex_top_right]
    rw [hSmap, ← MonoidHom.range_eq_map] at h1
    show ¬ 2 ∣ S.relIndex ⊤
    rw [Subgroup.relIndex_top_right, ← h1]
    exact hDs.2.2
  have hcard : Nat.card P = 5 * Nat.card S := by
    have h1 := Subgroup.relIndex_mul_card D Q
    rw [inf_of_le_left hDQ, h5] at h1
    rw [← Subgroup.card_map_of_injective (K := P) hinj, hPmap,
      ← Subgroup.card_map_of_injective (K := S) hinj, hSmap]
    exact h1.symm
  exact ⟨S, P, hSs, Subgroup.comap_mono hDQ, hcard, hSmap, hPmap⟩

theorem not_noFiveOver_of_inn614 {Y : Type} [Group Y] [Finite Y] (hZ : Subgroup.center Y = ⊥)
    {D Q : Subgroup (MulAut Y)} (hDs : IsSylowTwoOf D (MulAut.conj : Y →* MulAut Y).range)
    (hDQ : D ≤ Q) (hQN : Q ≤ (MulAut.conj : Y →* MulAut Y).range) (h5 : D.relIndex Q = 5) :
    ¬ FiveNorm.NoFiveOver Y := by
  obtain ⟨S, P, hSs, hSP, hcard, -, -⟩ := exists_pullback_inn614 hZ hDs hDQ hQN h5
  exact fun hno => hno S P hSs hSP hcard

end

theorem kg614FiveSpor_of_noFiveOver
    (hno : ∀ (W : Type) [Group W] [Finite W], (Ch1.AltList W ∨ Ch1.SporadicList W) →
      FiveNorm.NoFiveOver W) : KG614FiveSpor := by
  intro Γ _ _ H K T X hyp hW
  exfalso
  classical
  obtain ⟨-, -, hKq, -, hT2, hTK, hTs, -, hXO, hX5, hXn, hTX, hXK, hXinn, hXnt⟩ := hyp
  have hperf : commutator (ModO2 K) = ⊤ := by
    have := hKq.1
    exact Group.IsPerfect.commutator_eq_top
  have : IsSimpleGroup (ModO2 K ⧸ Subgroup.center (ModO2 K)) := hKq.2.1
  obtain ⟨a, b, hab⟩ := hKq.2.2
  have hZL := FiveNorm.center_eq_bot_of_isSimpleGroup hab
  have : Finite (MulAut (ModO2 K ⧸ Subgroup.center (ModO2 K))) :=
    Finite.of_injective _ DFunLike.coe_injective
  obtain ⟨h5, hQN⟩ := exists_five_overgroup614 (rho614 K) hXK hTK
    (inf_le_left : T ⊓ K ≤ T) inf_le_left inf_le_right hT2 hXn hX5 hXO hTX
    (fun x hx => rho614_mem_range (hXinn hx) (hXK hx)) (exists_rho614_ne_one hXK hperf hXnt)
    (isSylowTwoOf_rho614 hT2 hTs)
  exact not_noFiveOver_of_inn614 hZL (isSylowTwoOf_rho614 hT2 hTs) le_sup_right hQN h5
    (hno _ hW)

end CFSG.Quasithin.H13
