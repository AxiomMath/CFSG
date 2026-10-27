module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5111Rk2
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureFieldPrimeModelParameter
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalL2Two

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

theorem not_isPGroup_normalizer_of_bender {X : Type} [Group X]
    [Finite X] {k : ℕ} (hk : 2 ≤ k) (hX : LieModel X .PSL 2 2 k ∨ SuzukiModel X 2 k)
    {U : Subgroup X} (hU : IsSylowTwoOf U ⊤) :
    ¬ IsPGroup 2 ↥(Subgroup.normalizer (U : Set X)) := by
  intro h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx : ¬ 2 ∣ U.index := by
    have := hU.2.2
    rwa [← Subgroup.relIndex, Subgroup.relIndex_top_right] at this
  rcases hX with hL | hS
  ·
    have hcop : Nat.Coprime (Nat.card U) (U.relIndex (Subgroup.normalizer (U : Set X))) := by
      obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hU.2.1
      rw [hm]
      refine Nat.Coprime.pow_left m ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr ?_)
      exact fun h => hidx (h.trans (Subgroup.relIndex_dvd_index_of_le Subgroup.le_normalizer))
    obtain ⟨E, hEN, hUE, hUEs, -, -⟩ :=
      exists_complement_of_coprime Subgroup.le_normalizer le_rfl hcop
    obtain ⟨-, hcardE⟩ := l2TorusFact X k hk hL U E hU hEN (by rw [inf_comm]; exact hUE)
      (by rw [sup_comm]; exact hUEs)
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp (h2.to_le hEN)
    rw [hj] at hcardE
    have hk4 : 4 ≤ 2 ^ k := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    have hk2 : 2 ^ k = 2 * 2 ^ (k - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rcases j with _ | j
    · simp at hcardE
      omega
    · rw [pow_succ] at hcardE
      omega
  ·
    obtain ⟨-, a, ha, K, _, _, hf, hK, ⟨e₀⟩⟩ := hS
    let e : X ≃* CFSG.Open.Sz a := e₀.trans ((MulEquiv.subgroupCongr
      (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a K)).trans
        (CFSG.ShultStronglyClosedTI.glaSzEquivNative a ha (hf ▸ hK)))
    have hcard : Nat.card X = (2 ^ k) ^ 2 * (2 ^ k - 1) * ((2 ^ k) ^ 2 + 1) := by
      rw [Nat.card_congr e₀.toEquiv, hf, CFSG.LieType.Ree.suzuki_order (hf ▸ hK)]
    have hB : CFSG.BenderSuzuki.IsBorelSubgroup (Subgroup.normalizer (U : Set X)) := by
      have := h2.isNilpotent
      exact ⟨(inferInstance : Group.IsSolvable (Subgroup.normalizer (U : Set X))),
        IsPGroup.toSylow hU.2.1 hidx, rfl⟩
    obtain ⟨hindex, -⟩ :=
      CFSG.ShultStronglyClosedTI.CyclicSemiregular.suzuki_model_borel_parameter ha e _ hB
    rw [← hf] at hindex
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp h2
    have h1 := Subgroup.card_mul_index (Subgroup.normalizer (U : Set X))
    rw [hm, hindex, hcard] at h1
    have hpos : 0 < (2 ^ k) ^ 2 + 1 := by positivity
    have h3 : 2 ^ m = (2 ^ k) ^ 2 * (2 ^ k - 1) := by
      have := Nat.eq_of_mul_eq_mul_right hpos h1
      exact this
    have h4 : 2 ^ k - 1 ∣ 2 ^ m := ⟨(2 ^ k) ^ 2, by rw [h3, mul_comm]⟩
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h4
    have hk4 : 4 ≤ 2 ^ k := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    have hk2 : 2 ^ k = 2 * 2 ^ (k - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rcases j with _ | j
    · simp at hj
      omega
    · rw [pow_succ] at hj
      omega

section RankOne

variable {G : Type} [Group G] [Finite G]

theorem le_or_le_borelOf {T J Q : Subgroup G} (hRS : IsRankOneSylow (O2Q J))
    (hTJ : IsSylowTwoOf (T ⊓ J) J) (hTQ : T ⊓ J ≤ Q) (hQJ : Q ≤ J) :
    J ≤ Q ∨ Q ≤ borelOf J T := by
  have hOJ : pCoreOf 2 J ≤ T ⊓ J := F7.isSylowTwoOf_pCoreOf_le hTJ
  have hTt := Vol2.Ch11.SecS.isSylowTwoOf_modO2Image hTJ
  have hidx : ¬ 2 ∣ (modO2Image J (T ⊓ J)).index := by
    have := hTt.2.2
    rwa [← Subgroup.relIndex, Subgroup.relIndex_top_right] at this
  obtain ⟨-, hmax, -⟩ := hRS _ hTt.2.1 hidx
  by_cases hQ : modO2Image J Q = ⊤
  · left
    have h1 := Vol2.Ch11.SecS.le_sup_of_modO2Image_eq_top hQJ hQ
    rwa [sup_eq_left.mpr (hOJ.trans hTQ)] at h1
  · right
    have h1 := hmax _ (Subgroup.map_mono fun x hx => hTQ hx) hQ
    have h2 := h1.trans (normalizer_modO2Image_le (P := J ⊓ Subgroup.normalizer
      ((T ⊓ J : Subgroup G) : Set G)) inf_le_right hOJ le_rfl)
    have h3 := le_sup_of_modO2Image_le hQJ inf_le_left h2
    rwa [sup_eq_left.mpr (hOJ.trans (le_inf inf_le_right Subgroup.le_normalizer))] at h3

theorem not_le_normalizer_of_rankOne {T J : Subgroup G} (hRS : IsRankOneSylow (O2Q J))
    (hTJ : IsSylowTwoOf (T ⊓ J) J) :
    ¬ J ≤ Subgroup.normalizer ((T ⊓ J : Subgroup G) : Set G) := by
  intro hle
  have hTt := Vol2.Ch11.SecS.isSylowTwoOf_modO2Image hTJ
  have hidx : ¬ 2 ∣ (modO2Image J (T ⊓ J)).index := by
    have := hTt.2.2
    rwa [← Subgroup.relIndex, Subgroup.relIndex_top_right] at this
  obtain ⟨hne, -, -⟩ := hRS _ hTt.2.1 hidx
  apply hne
  rw [eq_top_iff, ← Vol2.Ch11.SecS.modO2Image_self J]
  exact Vol2.Ch11.SecS.modO2Image_le_normalizer hle

theorem exists_mem_borelOf_not_mem {T J : Subgroup G} {k : ℕ}
    (hk : 2 ≤ k) (hX : LieModel (O2Q J) .PSL 2 2 k ∨ SuzukiModel (O2Q J) 2 k)
    (hTJ : IsSylowTwoOf (T ⊓ J) J) : ∃ y ∈ borelOf J T, y ∉ T := by
  have hOJ : pCoreOf 2 J ≤ T ⊓ J := F7.isSylowTwoOf_pCoreOf_le hTJ
  have hTt := Vol2.Ch11.SecS.isSylowTwoOf_modO2Image hTJ
  have hnp := not_isPGroup_normalizer_of_bender hk hX hTt
  simp only [IsPGroup, not_forall, not_exists] at hnp
  obtain ⟨⟨x, hx⟩, hxn⟩ := hnp
  have hxU : x ∉ modO2Image J (T ⊓ J) := by
    intro hxU
    obtain ⟨e, he⟩ := hTt.2.1 ⟨x, hxU⟩
    exact hxn e (Subtype.ext (by simpa using congrArg Subtype.val he))
  obtain ⟨y, hy, rfl⟩ := normalizer_modO2Image_le (P := J ⊓ Subgroup.normalizer
    ((T ⊓ J : Subgroup G) : Set G)) inf_le_right hOJ le_rfl hx
  refine ⟨y, Subgroup.mem_subgroupOf.mp hy, fun hyT => hxU ⟨y, ?_, rfl⟩⟩
  exact Subgroup.mem_subgroupOf.mpr ⟨hyT, y.2⟩

end RankOne

section Two

variable {G : Type} [Group G] [Finite G] {T H K₁ K₂ : Subgroup G}

theorem inf_normalizer_borelOf_le {J : Subgroup G} (hRS : IsRankOneSylow (O2Q J))
    (hTJ : IsSylowTwoOf (T ⊓ J) J) :
    J ⊓ Subgroup.normalizer (borelOf J T : Set G) ≤ borelOf J T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTB : T ⊓ J ≤ borelOf J T := le_inf inf_le_right Subgroup.le_normalizer
  rcases le_or_le_borelOf hRS hTJ (le_inf (inf_le_right) (hTB.trans Subgroup.le_normalizer))
    inf_le_left with h | h
  · exfalso
    have hsyl : IsSylowTwoOf (T ⊓ J) (borelOf J T) := A4.isSylowTwoOf_mono hTJ hTB inf_le_left
    have hO : pCoreOf 2 (borelOf J T) = T ⊓ J :=
      le_antisymm (F7.isSylowTwoOf_pCoreOf_le hsyl)
        (le_pCoreOf_of_le_normalizer 2 hTB inf_le_right hTJ.2.1)
    apply not_le_normalizer_of_rankOne hRS hTJ
    rw [← hO]
    exact (h.trans inf_le_right).trans (normalizer_le_normalizer_pCoreOf 2 _)
  · exact h

theorem TwoComp.eq_of_isRankOneParabolicOver (tc : TwoComp T H K₁ K₂) (hK₁ : K₁ ∈ cComp H)
    (hTH : IsSylowTwoOf T H) (hRS₁ : IsRankOneSylow (O2Q K₁)) (hRS₂ : IsRankOneSylow (O2Q K₂))
    {P : Subgroup G} (hP : IsRankOneParabolicOver (oTwoUpper H) (T ⊓ oTwoUpper H) P) :
    P = K₁ ⊔ (oTwoUpper H ⊓ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G)) ∨
      P = K₂ ⊔ (oTwoUpper H ⊓ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := oTwoUpper H with hKdef
  set Bk := K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) with hBk
  obtain ⟨hBP, hPK, hmin⟩ := hP
  have hK₂ := tc.cK₂
  have hKH : K ≤ H := oTwoUpper_le H
  have hK₁K : K₁ ≤ K := le_sup_left.trans tc.sup.symm.le
  have hK₂K : K₂ ≤ K := le_sup_right.trans tc.sup.symm.le
  have hTK₁ : IsSylowTwoOf (T ⊓ K₁) K₁ := A312.isSylowTwoOf_inf_of_subnormal hK₁.2.2.1 hTH
  have hTK₂ : IsSylowTwoOf (T ⊓ K₂) K₂ := A312.isSylowTwoOf_inf_of_subnormal hK₂.2.2.1 hTH
  have hB₁ : borelOf K₁ T ≤ Bk := tc.borelOf_le hK₁ hTH
  have hB₂ : borelOf K₂ T ≤ Bk := (tc.symm hK₁).borelOf_le hK₂ hTH
  have hTB : ∀ {J : Subgroup G}, J ≤ K → T ⊓ J ≤ Bk := fun hJ =>
    le_inf (inf_le_right.trans hJ) ((inf_le_inf_left T hJ).trans Subgroup.le_normalizer)
  have hcase : ∀ {J : Subgroup G}, IsRankOneSylow (O2Q J) → IsSylowTwoOf (T ⊓ J) J → J ≤ K →
      J ≤ P → P = J ⊔ Bk := by
    intro J hRS hTJ hJK hJP
    refine (hmin _ (lt_of_le_of_ne le_sup_right fun he => ?_) (sup_le hJP hBP.le)).symm
    have hJB : J ≤ Bk := le_sup_left.trans he.ge
    refine not_le_normalizer_of_rankOne hRS hTJ fun y hy => ?_
    have h3 := Subgroup.inf_normalizer_le_normalizer_inf
      ⟨(hJB hy).2, Subgroup.le_normalizer hy⟩
    rwa [inf_assoc, inf_eq_right.mpr hJK] at h3
  rcases le_or_le_borelOf hRS₁ hTK₁ (le_inf ((hTB hK₁K).trans hBP.le) inf_le_right)
    (inf_le_right : P ⊓ K₁ ≤ K₁) with h1 | h1
  · exact Or.inl (hcase hRS₁ hTK₁ hK₁K (h1.trans inf_le_left))
  rcases le_or_le_borelOf hRS₂ hTK₂ (le_inf ((hTB hK₂K).trans hBP.le) inf_le_right)
    (inf_le_right : P ⊓ K₂ ≤ K₂) with h2 | h2
  · exact Or.inr (hcase hRS₂ hTK₂ hK₂K (h2.trans inf_le_left))
  exfalso
  refine hBP.ne (le_antisymm hBP.le fun p hp => ?_)
  have hK₂N : K₂ ≤ Subgroup.normalizer (K₁ : Set G) := le_normalizer_of_mem_cComp hK₁ hK₂
  have hKN₁ : K ≤ Subgroup.normalizer (K₁ : Set G) := by
    rw [show K = K₁ ⊔ K₂ from tc.sup]
    exact sup_le Subgroup.le_normalizer hK₂N
  have hpK : p ∈ K₁ ⊔ K₂ := (show K = K₁ ⊔ K₂ from tc.sup) ▸ hPK hp
  obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hK₂N).mp hpK
  have hOK₁ : pCoreOf 2 K₁ ≤ borelOf K₁ T :=
    (F7.isSylowTwoOf_pCoreOf_le hTK₁).trans (le_inf inf_le_right Subgroup.le_normalizer)
  have hOHK₁ : pCoreOf 2 H ⊓ K₁ ≤ pCoreOf 2 K₁ := by
    have hn : K₁ ≤ Subgroup.normalizer ((pCoreOf 2 H ⊓ K₁ : Subgroup G) : Set G) :=
      fun y hy => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨le_normalizer_pCoreOf 2 H ((le_of_mem_cComp hK₁) hy), Subgroup.le_normalizer hy⟩
    exact le_pCoreOf_of_le_normalizer 2 inf_le_right hn
      ((pCoreOf_isPGroup 2 H).to_le inf_le_left)
  have hk₁N : k₁ ∈ Subgroup.normalizer (borelOf K₁ T : Set G) := by
    refine mem_normalizer_of_conj_mem' fun b hb => ?_
    have hbK₁ : b ∈ K₁ := hb.1
    have hpb : k₁ * k₂ * b * (k₁ * k₂)⁻¹ ∈ borelOf K₁ T := by
      refine h1 ⟨?_, ?_⟩
      · exact P.mul_mem (P.mul_mem hp (hBP.le (hB₁ hb))) (P.inv_mem hp)
      · exact (Subgroup.mem_normalizer_iff.mp (hKN₁ (hPK hp)) b).mp hbK₁
    set π := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hπ
    have hk₂H : k₂ ∈ H := hK₂K.trans hKH hk₂
    have hbH : b ∈ H := (le_of_mem_cComp hK₁) hbK₁
    have hco : π ⟨b, hbH⟩ * π ⟨k₂, hk₂H⟩ = π ⟨k₂, hk₂H⟩ * π ⟨b, hbH⟩ :=
      tc.comm _ ⟨⟨b, hbH⟩, hbK₁, rfl⟩ _ ⟨⟨k₂, hk₂H⟩, hk₂, rfl⟩
    have ho : k₂ * b * k₂⁻¹ * b⁻¹ ∈ pCoreOf 2 K₁ := by
      refine hOHK₁ ⟨?_, ?_⟩
      · rw [← map_mul, ← map_mul, hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
          QuotientGroup.eq] at hco
        rw [Vol2.Ch11.SecS.pCoreOf_two_eq_map]
        refine ⟨_, (inferInstance : (CFSG.pCore 2 ↥H).Normal).conj_mem _ hco
          (⟨k₂, hk₂H⟩ * ⟨b, hbH⟩), ?_⟩
        simp [mul_assoc]
      · exact K₁.mul_mem ((Subgroup.mem_normalizer_iff.mp (hK₂N hk₂) b).mp hbK₁)
          (K₁.inv_mem hbK₁)
    have h3 : k₁ * (k₂ * b * k₂⁻¹ * b⁻¹) * k₁⁻¹ ∈ borelOf K₁ T :=
      hOK₁ ((Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 K₁ hk₁) _).mp ho)
    have h4 := (borelOf K₁ T).mul_mem ((borelOf K₁ T).inv_mem h3) hpb
    have h5 : (k₁ * (k₂ * b * k₂⁻¹ * b⁻¹) * k₁⁻¹)⁻¹ * (k₁ * k₂ * b * (k₁ * k₂)⁻¹) =
        k₁ * b * k₁⁻¹ := by group
    rwa [h5] at h4
  have hk₁B : k₁ ∈ Bk := hB₁ (inf_normalizer_borelOf_le hRS₁ hTK₁ ⟨hk₁, hk₁N⟩)
  have hk₂P : k₂ ∈ P ⊓ K₂ := by
    refine ⟨?_, hk₂⟩
    have := P.mul_mem (P.inv_mem (hBP.le hk₁B)) hp
    simpa using this
  exact Bk.mul_mem hk₁B (hB₂ (h2 hk₂P))

theorem TwoComp.le_normalizer_of_bender (tc : TwoComp T H K₁ K₂)
    (hK₁ : K₁ ∈ cComp H) (hTH : IsSylowTwoOf T H) {k : ℕ} (hk : 2 ≤ k)
    (hX : LieModel (O2Q K₁) .PSL 2 2 k ∨ SuzukiModel (O2Q K₁) 2 k) {S : Subgroup G}
    (hSH : S ≤ H) (hS2 : IsPGroup 2 S)
    (hBS : borelOf K₁ T ≤ Subgroup.normalizer (S : Set G)) :
    S ≤ Subgroup.normalizer (K₁ : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro s hs
  have hsH := hSH hs
  have hKH : oTwoUpper H ≤ H := oTwoUpper_le H
  have hK₁K : K₁ ≤ oTwoUpper H := le_sup_left.trans tc.sup.symm.le
  have hK₁c : K₁ ∈ cComp (oTwoUpper H) := cComp_mem_of_le hK₁ hK₁K hKH
  have hKs : K₁.map (MulAut.conj s).toMonoidHom ∈ cComp (oTwoUpper H) := by
    have h1 := cComp_map_mulEquiv (MulAut.conj s) hK₁c
    rwa [CFSG.LieType.Steinberg.mem_normalizer_iff_map_conj.mp
      (le_normalizer_oTwoUpper H hsH)] at h1
  rcases tc.cK _ hKs with h | h
  · exact A38.map_conj_eq_iff.mp h
  exfalso
  have hTK₁ : IsSylowTwoOf (T ⊓ K₁) K₁ := A312.isSylowTwoOf_inf_of_subnormal hK₁.2.2.1 hTH
  obtain ⟨y, hy, hyT⟩ := exists_mem_borelOf_not_mem hk hX hTK₁
  have hyK₁ : y ∈ K₁ := hy.1
  have hyH : y ∈ H := (le_of_mem_cComp hK₁) hyK₁
  have hx : y * s * y⁻¹ * s⁻¹ ∈ S :=
    S.mul_mem ((Subgroup.mem_normalizer_iff.mp (hBS hy) s).mp hs) (S.inv_mem hs)
  obtain ⟨e, he⟩ := hS2 ⟨_, hx⟩
  have he' : (y * s * y⁻¹ * s⁻¹) ^ 2 ^ e = 1 := by
    have := congrArg Subtype.val he
    simpa using this
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hπ
  have hzK₂ : s * y⁻¹ * s⁻¹ ∈ K₂ := by
    rw [← h]
    exact ⟨y⁻¹, K₁.inv_mem hyK₁, by simp [MulAut.conj_apply]⟩
  have hzH : s * y⁻¹ * s⁻¹ ∈ H := H.mul_mem (H.mul_mem hsH (H.inv_mem hyH)) (H.inv_mem hsH)
  have hyb : π ⟨y, hyH⟩ ∈ modO2Image H K₁ := ⟨⟨y, hyH⟩, hyK₁, rfl⟩
  have hzb : π ⟨_, hzH⟩ ∈ modO2Image H K₂ := ⟨⟨_, hzH⟩, hzK₂, rfl⟩
  have hcomm : Commute (π ⟨y, hyH⟩) (π ⟨_, hzH⟩) := tc.comm _ hyb _ hzb
  have hxb : π ⟨y, hyH⟩ * π ⟨_, hzH⟩ = π ⟨y * s * y⁻¹ * s⁻¹,
      H.mul_mem (H.mul_mem (H.mul_mem hyH hsH) (H.inv_mem hyH)) (H.inv_mem hsH)⟩ := by
    rw [← map_mul]
    congr 1
    apply Subtype.ext
    simp [mul_assoc]
  have hpow : π ⟨y, hyH⟩ ^ 2 ^ e * π ⟨_, hzH⟩ ^ 2 ^ e = 1 := by
    rw [← hcomm.mul_pow, hxb, ← map_pow]
    have : (⟨y * s * y⁻¹ * s⁻¹, H.mul_mem (H.mul_mem (H.mul_mem hyH hsH) (H.inv_mem hyH))
        (H.inv_mem hsH)⟩ : ↥H) ^ 2 ^ e = 1 := Subtype.ext (by simpa using he')
    rw [this, map_one]
  have hy1 : π ⟨y, hyH⟩ ^ 2 ^ e = 1 := by
    have h1 : π ⟨y, hyH⟩ ^ 2 ^ e ∈ modO2Image H K₁ ⊓ modO2Image H K₂ := by
      refine ⟨Subgroup.pow_mem _ hyb _, ?_⟩
      rw [eq_inv_of_mul_eq_one_left hpow]
      exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hzb _)
    rwa [tc.inf, Subgroup.mem_bot] at h1
  rw [← map_pow, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hy1
  obtain ⟨e', he''⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥H)) ⟨_, hy1⟩
  have hy2 : y ^ 2 ^ (e + e') = 1 := by
    have := congrArg (fun z : ↥(CFSG.pCore 2 ↥H) => ((z : ↥H) : G)) he''
    simp only [SubgroupClass.coe_pow, Subgroup.coe_one] at this
    rw [pow_add, pow_mul]
    simpa using this
  have hsyl : IsSylowTwoOf (T ⊓ K₁) (borelOf K₁ T) :=
    A4.isSylowTwoOf_mono hTK₁ (le_inf inf_le_right Subgroup.le_normalizer) inf_le_left
  have hz2 : IsPGroup 2 (Subgroup.zpowers y) :=
    IsPGroup.of_card (n := (orderOf y).factorization 2) (by
      rw [Nat.card_zpowers]
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hy2)
      rw [hj, Nat.factorization_pow_self Nat.prime_two])
  have h2 := IsPGroup.to_sup_of_normal_right' hz2 hsyl.2.1
    (le_trans ((Subgroup.zpowers_le).mpr hy) inf_le_right)
  have heq := hsyl.eq_of_le le_sup_right
    (sup_le ((Subgroup.zpowers_le).mpr hy) hsyl.1) h2
  have hyTK : y ∈ T ⊓ K₁ := by
    rw [← heq]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers y)
  exact hyT hyTK.1

theorem three_two (h38 : Vol2Native.A38ForSQTKCat)
    (hRL : RankOneListedFacts.{0}) {M L : Subgroup G} {n : ℕ} (hyp : Hyp5_1_8 G T M L H n)
    (hBorel : E2.IsBorelIn (oTwoUpper H) (M ⊓ oTwoUpper H)) (hK₁ : K₁ ∈ cComp H)
    (hKeq : oTwoUpper H = conjClosure K₁ T) (hlt : K₁ < oTwoUpper H) {k : ℕ} (hk : 2 ≤ k)
    (hX : LieModel (O2Q K₁) .PSL 2 2 k ∨ SuzukiModel (O2Q K₁) 2 k) :
    ∀ P : Subgroup G, IsRankOneParabolicOver (oTwoUpper H) (T ⊓ oTwoUpper H) P →
      pCoreOf 2 (M ⊓ H) ≤ Subgroup.normalizer (P : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hyp.toHyp5_0_1
  have : IsSimpleGroup G := h.simple
  have hloc : LocalSQTK G := (qtkeCore_of_cat h.nonabelian h.qtke).1
  have hTH : IsSylowTwoOf T H := h.isSylowTwoOf hyp.hStar.1.1
  have hMK := hyp.borel_eq hBorel
  have hOMK := hyp.pCoreOf_inf_oTwoUpper_eq hBorel
  obtain ⟨K₂', tc⟩ := exists_twoComp h38 hloc hyp.hStar.1.2 hTH hK₁ hKeq hlt
  have hKH : oTwoUpper H ≤ H := oTwoUpper_le H
  have hKN : H ≤ Subgroup.normalizer (oTwoUpper H : Set G) := le_normalizer_oTwoUpper H
  have hRL₁ : IsRankOneListed (O2Q K₁) := by
    rcases hX with hL | hS
    · exact isRankOneListed_of_lieModel (by omega) hL
    · obtain ⟨a, -, ⟨e⟩⟩ := exists_mulEquiv_sz_of_suzukiModel hS
      exact Or.inr (Or.inl ⟨a, ⟨e⟩⟩)
  have hRS₁ := hRL _ hRL₁
  have hRS₂ : IsRankOneSylow (O2Q K₂') := by
    obtain ⟨t, -, hK₂eq⟩ := tc.conj
    rw [hK₂eq]
    exact hRS₁.of_mulEquiv
      (A312.modO2Equiv (K₁.equivMapOfInjective _ (MulAut.conj t).injective))
  set S := pCoreOf 2 (M ⊓ H) with hSdef
  have hSH : S ≤ H := (pCoreOf_le 2 _).trans inf_le_right
  have hS2 : IsPGroup 2 S := pCoreOf_isPGroup 2 _
  have hBS : borelOf K₁ T ≤ Subgroup.normalizer (S : Set G) := by
    intro y hy
    have hyMK : y ∈ M ⊓ oTwoUpper H := by
      rw [hMK]
      exact tc.borelOf_le hK₁ hTH hy
    exact le_normalizer_pCoreOf 2 (M ⊓ H) ⟨hyMK.1, hKH hyMK.2⟩
  have hSK₁ := tc.le_normalizer_of_bender hK₁ hTH hk hX hSH hS2 hBS
  have hSK₂ : S ≤ Subgroup.normalizer (K₂' : Set G) := by
    intro s hs
    have hsH := hSH hs
    have hK₂K : K₂' ≤ oTwoUpper H := le_sup_right.trans tc.sup.symm.le
    have hK₂c : K₂' ∈ cComp (oTwoUpper H) := cComp_mem_of_le tc.cK₂ hK₂K hKH
    have hKs : K₂'.map (MulAut.conj s).toMonoidHom ∈ cComp (oTwoUpper H) := by
      have h1 := cComp_map_mulEquiv (MulAut.conj s) hK₂c
      rwa [CFSG.LieType.Steinberg.mem_normalizer_iff_map_conj.mp (hKN hsH)] at h1
    rcases tc.cK _ hKs with h1 | h1
    · exfalso
      apply tc.ne
      have h2 := map_mulAut_inv_map (MulAut.conj s) K₂'
      rw [h1, ← map_inv,
        CFSG.LieType.Steinberg.mem_normalizer_iff_map_conj.mp (hSK₁ (S.inv_mem hs))] at h2
      exact h2.symm
    · exact A38.map_conj_eq_iff.mp h1
  have hSTK : S ≤ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) := by
    rw [← hOMK]
    refine le_trans (fun s hs => ?_) (normalizer_le_normalizer_pCoreOf 2 (M ⊓ oTwoUpper H))
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer ((pCoreOf_le 2 _) hs).1, hKN (hSH hs)⟩
  have hSB : S ≤ Subgroup.normalizer ((oTwoUpper H ⊓ Subgroup.normalizer
      ((T ⊓ oTwoUpper H : Subgroup G) : Set G) : Subgroup G) : Set G) :=
    fun s hs => mem_normalizer_inf_normalizer (hKN (hSH hs)) (hSTK hs)
  intro P hP
  rcases tc.eq_of_isRankOneParabolicOver hK₁ hTH hRS₁ hRS₂ hP with rfl | rfl
  · exact F1.le_normalizer_sup hSK₁ hSB
  · exact F1.le_normalizer_sup hSK₂ hSB

end Two

theorem stmt5_1_11_three_of (hF : FactL2LieParabolic)
    (hG : FactRank2CartanGraph) (h38 : Vol2Native.A38ForSQTKCat) (hRL : RankOneListedFacts.{0})
    (hU3 : FactU3Cover) (h510 : Stmt5_1_10) : Stmt5_1_11_three := by
  intro G _ _ T M L H B D n hyp hN _
  obtain ⟨k, hk, hBorel, -, K₁, hK₁, hKeq, hcases⟩ := h510 G T M L H B D n hyp hN
  rcases hcases with ⟨hlt, hX⟩ | ⟨-, hbend⟩ | ⟨-, htype, -⟩
  · exact Or.inl (three_two h38 hRL hyp hBorel hK₁ hKeq hlt hk.1 hX)
  ·
    refine Or.inl fun P hP => ?_
    have h := hyp.toHyp5_0_1
    have hTH : IsSylowTwoOf T H := h.isSylowTwoOf hyp.hStar.1.1
    have hTK : IsSylowTwoOf (T ⊓ oTwoUpper H) (oTwoUpper H) :=
      A4.isSylowTwoOf_inf_normal hTH (oTwoUpper_le H) (le_normalizer_oTwoUpper H)
    have hRS := hRL _ (isRankOneListed_of_isBenderAny hU3 ⟨k, hk.1, hbend⟩)
    rcases le_or_le_borelOf hRS hTK
      ((le_inf inf_le_right Subgroup.le_normalizer).trans hP.1.le) hP.2.1 with h1 | h1
    · rw [le_antisymm hP.2.1 h1]
      exact ((pCoreOf_le 2 _).trans inf_le_right).trans (le_normalizer_oTwoUpper H)
    · exact absurd (lt_of_lt_of_le hP.1 h1) (lt_irrefl _)
  · exact three_rank2 hF hG hyp hBorel hk.1 htype

end CFSG.Quasithin.H13
