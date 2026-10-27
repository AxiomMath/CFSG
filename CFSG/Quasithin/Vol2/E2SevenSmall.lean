module

public import CFSG.Quasithin.Vol2.E2StatementsAS
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.ThirdParty.QiuzhenCFSG.BaerSuzuki.FinalTheorem
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralGenerators
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6

namespace E2

variable {G : Type} [Group G] [Finite G] {H T M V : Subgroup G}

omit [Finite G] in
theorem eq_one_of_mem_zpowers_of_pow_two_pow {c x : G} (hc : Odd (orderOf c))
    (hx : x ∈ Subgroup.zpowers c) {k : ℕ} (hk : x ^ 2 ^ k = 1) : x = 1 := by
  have h1 : orderOf x ∣ orderOf c := orderOf_dvd_of_mem_zpowers hx
  have h2 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h3 : Odd (orderOf x) := hc.of_dvd_nat h1
  have hcop : Nat.Coprime (orderOf x) (2 ^ k) :=
    Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr h3)
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop h2)

omit [Finite G] in
theorem mem_normalizer_of_forall_commute {U : Subgroup G} {g : G}
    (hg : ∀ u ∈ U, g * u = u * g) : g ∈ Subgroup.normalizer (U : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have : g * x * g⁻¹ = x := by rw [hg x hx]; group
    rw [this]
    exact hx
  · intro hx
    have h1 := hg _ hx
    have h2 : g * x * g⁻¹ = x := by
      calc g * x * g⁻¹ = g⁻¹ * (g * (g * x * g⁻¹)) := by group
        _ = g⁻¹ * ((g * x * g⁻¹) * g) := by rw [h1]
        _ = x := by group
    rw [← h2]
    exact hx

theorem Hyp28.isInIHTVC_of_dihedral (h : Hyp28 H T M V) {U : Subgroup G} {v c : G}
    (hUV : U ≤ V) (hv : v ∈ V) (hVU : V ≤ U ⊔ Subgroup.zpowers v) (hcH : c ∈ H)
    (hcU : ∀ u ∈ U, c * u = u * c) (hvc : v * c * v⁻¹ = c⁻¹) {p a : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (ha : 1 ≤ a) (hc : orderOf c = p ^ a) (hn : ∃ m : ℕ, E1.nParam H = m) :
    ASInputs.IsInIHTVC H T M V (V ⊔ conjSub c V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd (orderOf c) := hc ▸ (hp.odd_of_ne_two hp2).pow
  have hpa : 1 < p ^ a := Nat.one_lt_pow (by omega) hp.one_lt
  have hc1 : c ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hc
    omega
  have hV2 : ∀ x ∈ V, x ^ 2 = 1 := h.elem.2
  have hV2g : IsPGroup 2 V := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one]
    exact hV2 _ x.2)⟩
  have hVcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (h.elem.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hZV : ∀ x ∈ Subgroup.zpowers c, x ∈ V → x = 1 := fun x hx hxV =>
    eq_one_of_mem_zpowers_of_pow_two_pow (k := 1) hodd hx (by simpa using hV2 x hxV)
  have hvc' : v * c⁻¹ * v⁻¹ = c := by
    have := congrArg (·⁻¹) hvc
    simpa [mul_assoc] using this
  have hcv : c * v * c⁻¹ = c ^ 2 * v := by
    have h1 : v * c⁻¹ = c * v := by
      calc v * c⁻¹ = (v * c⁻¹ * v⁻¹) * v := by group
        _ = c * v := by rw [hvc']
    calc c * v * c⁻¹ = c * (v * c⁻¹) := by group
      _ = c * (c * v) := by rw [h1]
      _ = c ^ 2 * v := by rw [sq, mul_assoc]
  set I := V ⊔ conjSub c V with hIdef
  have hvI : v ∈ I := Subgroup.mem_sup_left hv
  have hcvI : c * v * c⁻¹ ∈ I := Subgroup.mem_sup_right (by
    rw [mem_conjSub]
    simpa [mul_assoc] using hv)
  have hc2I : c ^ 2 ∈ I := by
    have := I.mul_mem hcvI (I.inv_mem hvI)
    rwa [hcv, mul_inv_cancel_right] at this
  have hcI : c ∈ I := by
    obtain ⟨k, hk⟩ := hodd
    have e : (c ^ 2) ^ (k + 1) = c := by
      rw [← pow_mul, show 2 * (k + 1) = orderOf c + 1 by omega, pow_succ, pow_orderOf_eq_one,
        one_mul]
    rw [← e]
    exact I.pow_mem hc2I _
  set Z := Subgroup.zpowers c with hZdef
  have hNZ : ∀ g : G, g * c * g⁻¹ = c ∨ g * c * g⁻¹ = c⁻¹ →
      g ∈ Subgroup.normalizer (Z : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, hZdef, MonoidHom.map_zpowers]
    rcases hg with hg | hg
    · change Subgroup.zpowers (g * c * g⁻¹) = _
      rw [hg]
    · change Subgroup.zpowers (g * c * g⁻¹) = _
      rw [hg, Subgroup.zpowers_inv]
  have hUN : U ≤ Subgroup.normalizer (Z : Set G) := fun u hu =>
    hNZ u (Or.inl (by rw [← hcU u hu]; group))
  have hvN : v ∈ Subgroup.normalizer (Z : Set G) := hNZ v (Or.inr hvc)
  have hVN : V ≤ Subgroup.normalizer (Z : Set G) :=
    hVU.trans (sup_le hUN (Subgroup.zpowers_le.mpr hvN))
  have hIVZ : I = V ⊔ Z := by
    apply le_antisymm
    · refine sup_le le_sup_left ?_
      intro w hw
      rw [mem_conjSub] at hw
      have e : w = c * (c⁻¹ * w * c) * c⁻¹ := by group
      rw [e]
      exact (V ⊔ Z).mul_mem ((V ⊔ Z).mul_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers c))
        (Subgroup.mem_sup_left hw))
        (Subgroup.mem_sup_right (Z.inv_mem (Subgroup.mem_zpowers c)))
    · exact sup_le le_sup_left (Subgroup.zpowers_le.mpr hcI)
  have hIH : I ≤ H := by
    rw [hIVZ]
    exact sup_le h.le_H (Subgroup.zpowers_le.mpr hcH)
  have hidx : V.relIndex I = p ^ a := by
    rw [hIVZ, ← relIndex_inf_eq_relIndex_sup hVN]
    have hbot : V ⊓ Z = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      exact (Subgroup.mem_bot).mpr (hZV x hx.2 hx.1)
    rw [hbot, Subgroup.relIndex_bot_left, Nat.card_zpowers, hc]
  have hpodd : ¬ 2 ∣ p ^ a := (hp.odd_of_ne_two hp2).pow.not_two_dvd_nat
  have hVTI : V ≤ T ⊓ I := le_inf h.le_T le_sup_left
  have hsyl : IsSylowTwoOf (T ⊓ I) I := by
    refine ⟨inf_le_right, h.minParabolic.isSylow.2.1.to_le inf_le_left, fun hd => hpodd ?_⟩
    have e := Subgroup.relIndex_mul_relIndex V (T ⊓ I) I hVTI inf_le_right
    rw [← hidx, ← e]
    exact Dvd.dvd.mul_left hd _
  have hVM : V ≤ M := fun x hx => CFSG.LieType.BorelTits.pCoreOf_le 2 M (h.le_pCoreOf hx)
  have hMI : M ⊓ I = V := by
    apply le_antisymm
    · rintro x ⟨hxM, hxI⟩
      rw [hIVZ] at hxI
      have hxI' : x ∈ ((V ⊔ Z : Subgroup G) : Set G) := hxI
      rw [Subgroup.coe_mul_of_left_le_normalizer_right V Z hVN] at hxI'
      obtain ⟨w, hw, y, hy, rfl⟩ := hxI'
      have hwM : w ∈ M := hVM hw
      have hyM : y ∈ M := by
        have := M.mul_mem (M.inv_mem hwM) hxM
        simpa using this
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hvcj : v * c ^ j * v⁻¹ = (c ^ j)⁻¹ := by
        have := map_zpow (MulAut.conj v) c j
        rw [MulAut.conj_apply, MulAut.conj_apply, hvc, inv_zpow] at this
        exact this
      have hvP := h.le_pCoreOf hv
      have hcomm : v * c ^ j * v⁻¹ * (c ^ j)⁻¹ ∈ pCoreOf 2 M := by
        have h1 := (Subgroup.mem_normalizer_iff.mp
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M hyM) v⁻¹).mp
          ((pCoreOf 2 M).inv_mem hvP)
        have e : v * c ^ j * v⁻¹ * (c ^ j)⁻¹ = v * (c ^ j * v⁻¹ * (c ^ j)⁻¹) := by group
        rw [e]
        exact (pCoreOf 2 M).mul_mem hvP h1
      rw [hvcj] at hcomm
      obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M ⟨_, hcomm⟩
      have hk' : ((c ^ j)⁻¹ * (c ^ j)⁻¹) ^ 2 ^ k = 1 := by
        simpa using congrArg Subtype.val hk
      have hmem : (c ^ j)⁻¹ * (c ^ j)⁻¹ ∈ Z :=
        Z.mul_mem (Z.inv_mem (Subgroup.zpow_mem_zpowers c j))
          (Z.inv_mem (Subgroup.zpow_mem_zpowers c j))
      have h2 := eq_one_of_mem_zpowers_of_pow_two_pow hodd hmem hk'
      have h3 : (c ^ j) ^ 2 = 1 := by
        have := congrArg (·⁻¹) h2
        simpa [pow_two, mul_assoc] using this
      have h4 : c ^ j = 1 :=
        eq_one_of_mem_zpowers_of_pow_two_pow (k := 1) hodd (Subgroup.zpow_mem_zpowers c j)
          (by simpa using h3)
      simpa [h4] using hw
    · exact le_inf hVM le_sup_left
  have hkerV : kerIn (M ⊓ I) I ≤ V := hMI ▸ kerIn_le
  have hker2 : IsPGroup 2 (kerIn (M ⊓ I) I) := hV2g.to_le hkerV
  have hUker : U ≤ kerIn (M ⊓ I) I := by
    refine le_kerIn_of_le_normalizer (hMI ▸ hUV) ?_
    rw [hIVZ]
    refine sup_le (fun w hw => mem_normalizer_of_forall_commute fun u hu => hVcomm w hw u (hUV hu))
      (Subgroup.zpowers_le.mpr (mem_normalizer_of_forall_commute hcU))
  have h2cl : IsSylowTwoOf (pCoreOf 2 (kerIn (M ⊓ I) I)) (kerIn (M ⊓ I) I) := by
    have hKK : pCoreOf 2 (kerIn (M ⊓ I) I) = kerIn (M ⊓ I) I :=
      le_antisymm (CFSG.LieType.BorelTits.pCoreOf_le 2 _)
        (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_rfl Subgroup.le_normalizer hker2)
    rw [hKK]
    refine ⟨le_rfl, hker2, ?_⟩
    rw [Subgroup.subgroupOf_self, Subgroup.index_top]
    norm_num
  have hdih : Nonempty (StarQuot (M ⊓ I) I ≃* DihedralGroup (p ^ a)) := by
    set π := QuotientGroup.mk' ((kerIn (M ⊓ I) I).subgroupOf I) with hπ
    have hπ1 : ∀ x : ↥I, π x = 1 ↔ (x : G) ∈ kerIn (M ⊓ I) I := fun x => by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    set ρ := π ⟨c, hcI⟩ with hρ
    set σ := π ⟨v, hvI⟩ with hσ
    have hσ2 : σ ^ 2 = 1 := by
      rw [hσ, ← map_pow]
      have : (⟨v, hvI⟩ : ↥I) ^ 2 = 1 := Subtype.ext (by simpa using hV2 v hv)
      rw [this, map_one]
    have hrel : σ * ρ * σ⁻¹ = ρ⁻¹ := by
      rw [hσ, hρ, ← map_inv, ← map_mul, ← map_mul, ← map_inv]
      congr 1
      exact Subtype.ext (by simpa using hvc)
    have hord : orderOf ρ = p ^ a := by
      apply Nat.dvd_antisymm
      · rw [← hc, ← Subgroup.orderOf_mk c hcI]
        exact orderOf_map_dvd π _
      · rw [← hc]
        apply orderOf_dvd_of_pow_eq_one
        have h1 : π (⟨c, hcI⟩ ^ orderOf ρ) = 1 := by rw [map_pow, ← hρ, pow_orderOf_eq_one]
        rw [hπ1] at h1
        have h2 : c ^ orderOf ρ ∈ V := hkerV (by simpa using h1)
        exact hZV _ (Subgroup.npow_mem_zpowers c _) h2
    have hσρ : σ ∉ Subgroup.zpowers ρ := by
      intro hmem
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem
      have h1 : π (⟨v, hvI⟩ * (⟨c, hcI⟩ ^ j)⁻¹) = 1 := by
        rw [map_mul, map_inv, map_zpow, ← hρ, ← hσ, hj, mul_inv_cancel]
      rw [hπ1] at h1
      have h2 : v * (c ^ j)⁻¹ ∈ V := hkerV (by simpa using h1)
      have h3 : (c ^ j)⁻¹ ∈ V := by
        have := V.mul_mem (V.inv_mem hv) h2
        simpa [mul_assoc] using this
      have h4 : (c ^ j)⁻¹ = 1 := hZV _ (Z.inv_mem (Subgroup.zpow_mem_zpowers c j)) h3
      have h5 : v ∈ kerIn (M ⊓ I) I := by
        have := (h1 : _)
        simpa [h4] using h1
      have h6 : c * v * c⁻¹ ∈ M ⊓ I := (mem_kerIn.mp h5) c hcI
      rw [hMI, hcv] at h6
      have h7 : c ^ 2 ∈ V := by
        have := V.mul_mem h6 (V.inv_mem hv)
        simpa using this
      have h8 : c ^ 2 = 1 := hZV _ (Subgroup.npow_mem_zpowers c 2) h7
      exact hc1 (eq_one_of_mem_zpowers_of_pow_two_pow (k := 1) hodd (Subgroup.mem_zpowers c)
        (by simpa using h8))
    have hgen : (⊤ : Subgroup (StarQuot (M ⊓ I) I)) =
        Subgroup.zpowers ρ ⊔ Subgroup.zpowers σ := by
      refine le_antisymm ?_ le_top
      rintro y -
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ y
      set S := ((Subgroup.zpowers ρ ⊔ Subgroup.zpowers σ).comap π).map I.subtype with hS
      have hUS : U ≤ S := by
        intro u hu
        refine Subgroup.mem_map.mpr ⟨⟨u, le_sup_left (a := V) (hUV hu)⟩, ?_, rfl⟩
        rw [Subgroup.mem_comap, (hπ1 _).mpr (hUker hu)]
        exact Subgroup.one_mem _
      have hvS : v ∈ S := Subgroup.mem_map.mpr ⟨⟨v, hvI⟩,
        Subgroup.mem_comap.mpr (Subgroup.mem_sup_right (Subgroup.mem_zpowers σ)), rfl⟩
      have hcS : c ∈ S := Subgroup.mem_map.mpr ⟨⟨c, hcI⟩,
        Subgroup.mem_comap.mpr (Subgroup.mem_sup_left (Subgroup.mem_zpowers ρ)), rfl⟩
      have hIS : I ≤ S := by
        rw [hIVZ]
        exact sup_le (hVU.trans (sup_le hUS (Subgroup.zpowers_le.mpr hvS)))
          (Subgroup.zpowers_le.mpr hcS)
      obtain ⟨x', hx', hxx⟩ := Subgroup.mem_map.mp (hIS x.2)
      have : x' = x := Subtype.ext hxx
      rw [← this]
      exact Subgroup.mem_comap.mp hx'
    have := CFSG.GorensteinWalter.dihedral_of_generators_of_not_mem ρ σ hgen hσ2 hrel hσρ
    rwa [hord] at this
  obtain ⟨m, hm⟩ := hn
  exact ⟨hIH, ⟨c, hcI, rfl⟩, hsyl, h2cl, 1, ⟨m, by rw [hm, one_mul]⟩,
    Or.inr (Or.inl ⟨rfl, p, a, hp, hp2, ha, hdih⟩)⟩

theorem Hyp28.exists_isInIHTVC_of_card_two (h : Hyp28 H T M V) (hJ : kerIn M H = ⊥)
    (hV : Nat.card V = 2) (hn : ∃ m : ℕ, E1.nParam H = m) :
    ∃ I : Subgroup G, ASInputs.IsInIHTVC H T M V I := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO2 : pCoreOf 2 H = ⊥ := le_bot_iff.mp (hJ ▸ h.minParabolic.pCoreOf_le_kerIn)
  have hnt : Nontrivial ↥V := Finite.one_lt_card_iff_nontrivial.mp (by rw [hV]; norm_num)
  obtain ⟨⟨v, hvV⟩, hv1⟩ := exists_ne (1 : ↥V)
  have hv1' : v ≠ 1 := fun h1 => hv1 (Subtype.ext h1)
  have hv2 : v ^ 2 = 1 := h.elem.2 v hvV
  have hordv : orderOf v = 2 := orderOf_eq_prime hv2 hv1'
  have hVv : V ≤ Subgroup.zpowers v := by
    have hle : Subgroup.zpowers v ≤ V := Subgroup.zpowers_le.mpr hvV
    have hcard : Nat.card V ≤ Nat.card (Subgroup.zpowers v) := by rw [Nat.card_zpowers, hordv, hV]
    exact (Subgroup.eq_of_le_of_card_ge hle hcard).ge
  have hvH : v ∈ H := h.le_H hvV
  set x : ↥H := ⟨v, hvH⟩ with hxdef
  have hx2' : x ^ 2 = 1 := Subtype.ext (by simpa [hxdef] using hv2)
  have hx1 : x ≠ 1 := fun h1 => hv1' (congrArg Subtype.val h1)
  have hx2 : IsPGroup 2 (Subgroup.zpowers x) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime hx2' hx1
  have hxO : x ∉ CFSG.pCore 2 ↥H := by
    intro hxm
    have hvP : v ∈ pCoreOf 2 H := by
      show v ∈ (CFSG.Open.pCore 2 ↥H).map H.subtype
      exact Subgroup.mem_map.mpr ⟨x, hxm, rfl⟩
    rw [hO2] at hvP
    exact hv1' ((Subgroup.mem_bot).mp hvP)
  obtain ⟨g, hg⟩ : ∃ g : ↥H, ¬ IsPGroup 2 (Subgroup.closure ({x, g * x * g⁻¹} : Set ↥H)) := by
    by_contra hall
    push Not at hall
    exact hxO (CFSG.BaerSuzuki.baer_suzuki x hx2 hall)
  set w := g * x * g⁻¹ with hw
  have hw2 : w ^ 2 = 1 := by
    rw [hw, sq]
    calc g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
      _ = 1 := by rw [← sq, hx2', mul_one, mul_inv_cancel]
  set c₀ := x * w with hc₀
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right (by rw [← sq, hx2'])
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right (by rw [← sq, hw2])
  have hxc : x * c₀ * x⁻¹ = c₀⁻¹ := by
    rw [hc₀, mul_inv_rev, hxinv, hwinv]
    calc x * (x * w) * x = (x * x) * w * x := by group
      _ = w * x := by rw [← sq, hx2', one_mul]
  have hxN : x ∈ Subgroup.normalizer (Subgroup.zpowers c₀ : Set ↥H) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    change Subgroup.zpowers (x * c₀ * x⁻¹) = _
    rw [hxc, Subgroup.zpowers_inv]
  have hnot2 : ¬ ∃ k : ℕ, c₀ ^ 2 ^ k = 1 := by
    rintro ⟨k, hk⟩
    apply hg
    have hc2 : IsPGroup 2 (Subgroup.zpowers c₀) := by
      refine IsPGroup.of_card (n := (orderOf c₀).factorization 2) ?_
      rw [Nat.card_zpowers]
      have hd : orderOf c₀ ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
      obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
      rw [hi', Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same]
    have hsup := IsPGroup.to_sup_of_normal_right' hx2 hc2 (Subgroup.zpowers_le.mpr hxN)
    refine hsup.to_le ((Subgroup.closure_le _).mpr ?_)
    intro y hy
    rcases hy with rfl | hy
    · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
    · rw [Set.mem_singleton_iff] at hy
      rw [hy]
      have e : w = x⁻¹ * c₀ := by rw [hc₀, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.inv_mem _ (Subgroup.mem_zpowers _)))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  have hn0 : orderOf c₀ ≠ 0 := (orderOf_pos c₀).ne'
  obtain ⟨p, hp, hpd, hp2⟩ : ∃ p, p.Prime ∧ p ∣ orderOf c₀ ∧ p ≠ 2 := by
    by_contra hno
    push Not at hno
    apply hnot2
    refine ⟨(orderOf c₀).primeFactorsList.length, ?_⟩
    rw [← Nat.eq_prime_pow_of_unique_prime_dvd hn0 (fun {d} hd hdd => hno d hd hdd)]
    exact pow_orderOf_eq_one c₀
  set c := c₀ ^ (orderOf c₀ / p) with hcdef
  have hcord : orderOf c = p := orderOf_pow_orderOf_div hn0 hpd
  have hxc' : x * c * x⁻¹ = c⁻¹ := by
    have := map_pow (MulAut.conj x) c₀ (orderOf c₀ / p)
    rw [MulAut.conj_apply, MulAut.conj_apply, hxc, inv_pow] at this
    exact this
  have hvc : v * (c : G) * v⁻¹ = (c : G)⁻¹ := by
    have := congrArg Subtype.val hxc'
    simpa [hxdef] using this
  refine ⟨_, h.isInIHTVC_of_dihedral (U := ⊥) bot_le hvV (by rw [bot_sup_eq]; exact hVv) c.2
    (fun u hu => by rw [(Subgroup.mem_bot).mp hu, mul_one, one_mul]) hvc hp hp2 le_rfl ?_ hn⟩
  rw [Subgroup.orderOf_coe, hcord, pow_one]

theorem Hyp28.exists_isInIHTVC_of_solvable (h : Hyp28 H T M V) (hJ : kerIn M H = ⊥)
    (hsolv : Group.IsSolvable ↥H) : ∃ I : Subgroup G, ASInputs.IsInIHTVC H T M V I := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmp := h.minParabolic.subgroupOf
  have hJ' : kerIn (M.subgroupOf H) ⊤ = ⊥ := by
    rw [kerIn_subgroupOf_top, hJ, Subgroup.bot_subgroupOf]
  obtain ⟨p, hp, hp2, hZ⟩ := hmp.exists_odd_prime_of_solvable hsolv
  obtain ⟨hKp, -⟩ := hmp.twoResidual_isPGroup_of_solvable hJ' hsolv hZ
  have hKH : twoResidual H ≤ H := twoResidual_le H
  have hKp' : IsPGroup p (twoResidual H) := by
    rw [twoResidual_top_eq_subgroupOf] at hKp
    exact hKp.of_equiv (Subgroup.subgroupOfEquivOfLe hKH)
  have hHK : H ≤ Subgroup.normalizer (twoResidual H : Set G) := le_normalizer_twoResidual H
  obtain ⟨v, hv, y, hyK, hvy⟩ : ∃ v ∈ V, ∃ y ∈ twoResidual H, v * y ≠ y * v := by
    by_contra hall
    push Not at hall
    apply h.not_le_normalizer
    rw [← sup_twoResidual_eq h.minParabolic.isSylow]
    refine sup_le h.normal_T fun y hy => ?_
    exact mem_normalizer_of_forall_commute fun u hu => (hall u hu y hy).symm
  have hVK : V ≤ Subgroup.normalizer (twoResidual H : Set G) := h.le_H.trans hHK
  let : MulDistribMulAction ↥V ↥(twoResidual H) :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer V (twoResidual H) hVK
  have : IsElementaryAbelian 2 ↥V :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 V).mpr h.elem
  have : Nontrivial ↥V := (Subgroup.nontrivial_iff_ne_bot V).mpr h.ne_bot
  have hKodd : ¬ 2 ∣ Nat.card ↥(twoResidual H) := by
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hKp'
    rw [hn]
    intro hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
      (Nat.prime_two.dvd_of_dvd_pow hd)).symm
  have hgen := SolvableHall.coprime_hyperplane_generation (p := 2) (A := ↥V)
    (H := ↥(twoResidual H)) hKodd
  obtain ⟨B, hB, q, hqK, hqB, hvq⟩ : ∃ B : Subgroup ↥V, B.index = 2 ∧ ∃ q ∈ twoResidual H,
      (∀ b : ↥V, b ∈ B → (b : G) * q = q * (b : G)) ∧ v * q ≠ q * v := by
    by_contra hno
    push Not at hno
    have hle : (⨆ (B' : Subgroup ↥V) (_ : B'.index = 2),
        CFSG.fixedPointSubgroup B' ↥(twoResidual H)) ≤
        (Subgroup.centralizer ({v} : Set G)).subgroupOf (twoResidual H) := by
      refine iSup₂_le fun B' hB' q hq => ?_
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
      have hq' : ∀ b : ↥V, b ∈ B' → (b : G) * q * (b : G)⁻¹ = q := fun b hb =>
        congrArg Subtype.val (hq ⟨b, hb⟩)
      refine (hno B' hB' q q.2 fun b hb => ?_).symm
      have h1 := hq' b hb
      calc (b : G) * q = (b : G) * q * (b : G)⁻¹ * b := by group
        _ = q * b := by rw [h1]
    have hy' : (⟨y, hyK⟩ : ↥(twoResidual H)) ∈ (⊤ : Subgroup ↥(twoResidual H)) := Subgroup.mem_top _
    rw [← hgen] at hy'
    have h2 := hle hy'
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff] at h2
    exact hvy h2.symm
  set U := B.map V.subtype with hUdef
  have hUV : U ≤ V := Subgroup.map_subtype_le B
  have hvU : (⟨v, hv⟩ : ↥V) ∉ B := fun hvB => hvq (hqB ⟨v, hv⟩ hvB)
  have hVU : V ≤ U ⊔ Subgroup.zpowers v := by
    intro x hx
    by_cases hxB : (⟨x, hx⟩ : ↥V) ∈ B
    · exact Subgroup.mem_sup_left ⟨⟨x, hx⟩, hxB, rfl⟩
    · have hxv : (⟨x, hx⟩ : ↥V) * ⟨v, hv⟩ ∈ B :=
        (Subgroup.mul_mem_iff_of_index_two hB).mpr ⟨fun h1 => (hxB h1).elim,
          fun h1 => (hvU h1).elim⟩
      have hU : x * v ∈ U := ⟨_, hxv, rfl⟩
      have e : x = (x * v) * v⁻¹ := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hU)
        (Subgroup.mem_sup_right (Subgroup.inv_mem _ (Subgroup.mem_zpowers v)))
  have hv2 : v * v = 1 := by rw [← sq]; exact h.elem.2 v hv
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  have hcommV : ∀ {x y : G}, x ∈ V → y ∈ V → x * y = y * x := fun {x y} hx hy =>
    congrArg Subtype.val (h.elem.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hvH : v ∈ H := h.le_H hv
  set c := q⁻¹ * (v * q * v⁻¹) with hcdef
  have hcK : c ∈ twoResidual H := (twoResidual H).mul_mem ((twoResidual H).inv_mem hqK)
    ((Subgroup.mem_normalizer_iff.mp (hHK hvH) q).mp hqK)
  have hcH : c ∈ H := hKH hcK
  have hcU : ∀ u ∈ U, c * u = u * c := by
    rintro _ ⟨b, hb, rfl⟩
    have hbq := hqB b hb
    have hbv : (b : G) * v = v * b := (hcommV b.2 hv)
    show c * (b : G) = (b : G) * c
    rw [hcdef]
    have hbq' : (b : G) * q⁻¹ = q⁻¹ * b := by
      calc (b : G) * q⁻¹ = q⁻¹ * (q * b) * q⁻¹ := by group
        _ = q⁻¹ * (b * q) * q⁻¹ := by rw [hbq]
        _ = q⁻¹ * b := by group
    have hbv' : (b : G) * v⁻¹ = v⁻¹ * b := by
      calc (b : G) * v⁻¹ = v⁻¹ * (v * b) * v⁻¹ := by group
        _ = v⁻¹ * (b * v) * v⁻¹ := by rw [hbv]
        _ = v⁻¹ * b := by group
    calc q⁻¹ * (v * q * v⁻¹) * b = q⁻¹ * v * q * (v⁻¹ * b) := by group
      _ = q⁻¹ * v * q * (b * v⁻¹) := by rw [hbv']
      _ = q⁻¹ * v * (q * b) * v⁻¹ := by group
      _ = q⁻¹ * v * (b * q) * v⁻¹ := by rw [hbq]
      _ = q⁻¹ * (v * b) * q * v⁻¹ := by group
      _ = q⁻¹ * (b * v) * q * v⁻¹ := by rw [hbv]
      _ = (q⁻¹ * b) * v * q * v⁻¹ := by group
      _ = (b * q⁻¹) * v * q * v⁻¹ := by rw [hbq']
      _ = b * (q⁻¹ * (v * q * v⁻¹)) := by group
  have hvc : v * c * v⁻¹ = c⁻¹ := by
    rw [hcdef]
    have e1 : (q⁻¹ * (v * q * v⁻¹))⁻¹ = v * q⁻¹ * v⁻¹ * q := by group
    rw [e1, hvinv]
    calc v * (q⁻¹ * (v * q * v)) * v = v * q⁻¹ * v * q * (v * v) := by group
      _ = v * q⁻¹ * v * q := by rw [hv2, mul_one]
  have hc1 : c ≠ 1 := by
    intro h1
    apply hvq
    have e : v * q * v⁻¹ = q := by
      have := congrArg (q * ·) h1
      simpa [hcdef, mul_assoc] using this
    calc v * q = (v * q * v⁻¹) * v := by group
      _ = q * v := by rw [e]
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha⟩ := IsPGroup.iff_orderOf.mp hKp' ⟨c, hcK⟩
  rw [Subgroup.orderOf_mk] at ha
  have ha1 : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with rfl | h0
    · rw [pow_zero, orderOf_eq_one_iff] at ha
      exact (hc1 ha).elim
    · exact h0
  have hn : ∃ m : ℕ, E1.nParam H = m := by
    have h1 := E1.solvable_nParam_le_one hsolv
    have h2 : E1.nParam H ≠ ⊤ := ne_top_of_le_ne_top (by simp) h1
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp h2
    exact ⟨m, hm.symm⟩
  exact ⟨_, h.isInIHTVC_of_dihedral hUV hv hVU hcH hcU hvc hp hp2 ha1 ha hn⟩

end E2

end CFSG.Quasithin
