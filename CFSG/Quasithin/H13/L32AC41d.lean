module

public import CFSG.Quasithin.H13.L32AC41b

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

theorem map_eq_one_of_odd {X Y : Type*} [Group X] [Group Y] (f : X →* Y) {w : X}
    (hw : Odd (orderOf w)) {k : ℕ} (hk : f w ^ 2 ^ k = 1) : f w = 1 := by
  have h1 : Odd (orderOf (f w)) := Odd.of_dvd_nat hw (orderOf_map_dvd f w)
  have h2 : Nat.Coprime (orderOf (f w)) (2 ^ k) :=
    Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr h1)
  exact orderOf_eq_one_iff.mp (h2.eq_one_of_dvd (orderOf_dvd_of_pow_eq_one hk))

theorem sl2_comm_ra : ∀ a r : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2), a ≠ 1 → a ^ 3 = 1 →
    r ≠ 1 → r ^ 2 = 1 → r * a * r⁻¹ * a⁻¹ = a := by
  decide

theorem sl2_comm_raa : ∀ a r : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2), a ≠ 1 → a ^ 3 = 1 →
    r ≠ 1 → r ^ 2 = 1 → r * (a * a) * r⁻¹ * (a * a)⁻¹ = a * a := by
  decide

theorem sl2_comm_ab : ∀ a b : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2), a ≠ 1 → a ^ 3 = 1 →
    b ≠ 1 → b ^ 2 = 1 → a * b * a⁻¹ * b⁻¹ = a * a := by
  decide

theorem sl2_comm' (a r β : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) (ha1 : a ≠ 1)
    (ha3 : a ^ 3 = 1) (hr1 : r ≠ 1) (hr2 : r ^ 2 = 1) (hβ1 : β ≠ 1) :
    r * β * r⁻¹ * β⁻¹ = a ∨ r * β * r⁻¹ * β⁻¹ = a * a ∨
      a * β * a⁻¹ * β⁻¹ = a ∨ a * β * a⁻¹ * β⁻¹ = a * a := by
  rcases sl2_trich a β ha1 ha3 with h | h | h | h
  · exact absurd h hβ1
  · rw [h]
    exact Or.inl (sl2_comm_ra a r ha1 ha3 hr1 hr2)
  · rw [h]
    exact Or.inr (Or.inl (sl2_comm_raa a r ha1 ha3 hr1 hr2))
  · exact Or.inr (Or.inr (Or.inr (sl2_comm_ab a β ha1 ha3 hβ1 h)))

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

theorem l1T_le_normalizer_szS1' (hN1 : LieSylowOver3) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (S : Setting147 G T L V H) {K : Subgroup G} (hK : K ∈ cComp H)
    (hq : CFSG.IsQuasisimple (cStar K)) (hKn : H ≤ Subgroup.normalizer (K : Set G)) {n : ℕ}
    (hn : 1 < n) (hLie : A315.IsLieChar2 n (cStar K ⧸ Subgroup.center (cStar K))) :
    modO2Image H (l1 T L V ⊔ T) ≤
      Subgroup.normalizer (szS1 T H K : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Kb := modO2Image H K with hKb
  set S₁ := szS1 T H K with hS₁
  set N₀ := modO2Image H (l1 T L V ⊔ T) with hN₀
  set Y₀ := N₀ ⊓ Kb with hY₀
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hS := isSylowIn_szS1_of S hK
  have hSY : S₁ ≤ Y₀ :=
    le_inf (inf_le_left.trans (Subgroup.map_mono fun x hx =>
      ((le_sup_right : T ≤ l1 T L V ⊔ T) hx : (x : G) ∈ l1 T L V ⊔ T))) inf_le_right
  have hYK : Y₀ ≤ Kb := inf_le_right
  have hodd : Odd (S₁.relIndex Y₀) := by
    have hmul := Subgroup.relIndex_mul_relIndex S₁ Y₀ Kb hSY hYK
    have h2 : ¬ 2 ∣ S₁.relIndex Kb := hS.not_dvd_relIndex
    refine Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp fun hd => h2 ?_)
    rw [← hmul]
    exact Dvd.dvd.mul_right hd _
  obtain ⟨a, ha⟩ : ∃ a : ℕ, S₁.relIndex Y₀ ∣ 3 * 2 ^ a := by
    obtain ⟨a, ha⟩ := card_l1T_mod_dvd h1222 h1332 h1334 S
    exact ⟨a, (Dvd.intro _ (Subgroup.relIndex_mul_card S₁ Y₀)).trans
      ((Subgroup.card_dvd_of_le inf_le_left).trans ha)⟩
  have hY0 : Y₀ ≤ Subgroup.normalizer (S₁ : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
    rcases eq_one_or_three_of_odd_dvd hodd ha with h1 | h3
    · exact (Subgroup.relIndex_eq_one.mp h1).trans Subgroup.le_normalizer
    · obtain ⟨hqX, hoddX, hLieX⟩ := kst_props hK hq hLie
      have h := hN1 (↥Kb) n hn hqX hoddX hLieX (S₁.subgroupOf Kb) (Y₀.subgroupOf Kb)
        (isSylowTwoOf_subgroupOf hS) (fun x hx => hSY hx)
        (by rw [Subgroup.relIndex_subgroupOf hYK]; exact h3)
      intro y hy
      exact (mem_normalizer_subgroupOf_iff hS.le ⟨y, hYK hy⟩).mp
        (h (show (⟨y, hYK hy⟩ : ↥Kb) ∈ Y₀.subgroupOf Kb from hy))
  have hP2 : ∀ P : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H), IsPGroup 2 ↥P → P ≤ Y₀ → P ≤ S₁ := by
    intro P hP hPY
    have hA : IsPGroup 2 ↥(P ⊔ S₁) := hP.to_sup_of_normal_right' hS.isPGroup (hPY.trans hY0)
    have hAY : P ⊔ S₁ ≤ Y₀ := sup_le hPY hSY
    have h1 : Odd (S₁.relIndex (P ⊔ S₁)) := by
      have hmul := Subgroup.relIndex_mul_relIndex S₁ (P ⊔ S₁) Y₀ le_sup_right hAY
      exact (Nat.odd_mul.mp (hmul ▸ hodd)).1
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp hA
    have h2 : S₁.relIndex (P ⊔ S₁) ∣ 2 ^ k := by
      rw [← hk]
      exact Dvd.intro _ (Subgroup.relIndex_mul_card S₁ (P ⊔ S₁))
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
    have hj0 : j = 0 := by
      rcases j with _ | j
      · rfl
      · exfalso
        rw [hj, pow_succ] at h1
        exact (Nat.not_even_iff_odd.mpr h1) (even_two.mul_left _)
    rw [hj0, pow_zero, Subgroup.relIndex_eq_one] at hj
    exact le_sup_left.trans hj
  have hKbN : Kb.Normal := by
    have : (K.subgroupOf H).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hKn
    exact Subgroup.Normal.map this _ (QuotientGroup.mk'_surjective _)
  intro z hz
  have hPY : S₁.map (MulAut.conj z).toMonoidHom ≤ Y₀ := by
    rintro _ ⟨s, hs, rfl⟩
    have hsY := hSY hs
    show z * s * z⁻¹ ∈ Y₀
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact N₀.mul_mem (N₀.mul_mem hz (Subgroup.mem_inf.mp hsY).1) (N₀.inv_mem hz)
    · exact hKbN.conj_mem _ (Subgroup.mem_inf.mp hsY).2 z
  have hle := hP2 _ (hS.isPGroup.map _) hPY
  refine Subgroup.mem_normalizer_fintype fun s hs => ?_
  exact hle ⟨s, hs, rfl⟩

theorem isSolvable_szB1_l1T' (hN1 : LieSylowOver3) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (S : Setting147 G T L V H) {K : Subgroup G} (hK : K ∈ cComp H)
    (hq : CFSG.IsQuasisimple (cStar K)) (hKn : H ≤ Subgroup.normalizer (K : Set G)) {n : ℕ}
    (hn : 1 < n) (hLie : A315.IsLieChar2 n (cStar K ⧸ Subgroup.center (cStar K))) :
    Group.IsSolvable ↥(szB1 T H K ⊔ modO2Image H (l1 T L V ⊔ T)) := by
  have hN := l1T_le_normalizer_szS1' hN1 h1222 h1332 h1334 S hK hq hKn hn hLie
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hBN : modO2Image H (l1 T L V ⊔ T) ≤
      Subgroup.normalizer (szB1 T H K : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
    intro z hz
    have hzS := hN hz
    obtain ⟨w, -, rfl⟩ := mem_modO2Image'.mp hz
    exact mem_normalizer_szB1 hzS (mk_mem_normalizer hKH (hKn w.2))
  exact isSolvable_sup_of_le_normalizer' hBN (isSolvable_szB1_of S hK)
    (isSolvable_l1T_star h1222 h1332 h1334 S)

theorem l1_le_of_star_le (S : Setting147 G T L V H) {K : Subgroup G} (hK : K ∈ cComp H)
    (hKn : H ≤ Subgroup.normalizer (K : Set G))
    (hle : modO2Image H (l1 T L V) ≤ modO2Image H K) : l1 T L V ≤ K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hTH : T ≤ H := Setting147.TH' S
  have hKs : (K.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hKn
  show Subgroup.closure _ ≤ K
  refine (Subgroup.closure_le _).mpr ?_
  intro w hw
  have hwl : w ∈ l1 T L V := Subgroup.subset_closure hw
  have hwo := hw.2
  have hwH : w ∈ H := Setting147.l1H' S hwl
  have hwo' : Odd (orderOf (⟨w, hwH⟩ : ↥H)) := by rwa [Subgroup.orderOf_mk]
  have hwK : QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨w, hwH⟩ ∈ modO2Image H K :=
    hle (mem_modO2Image'.mpr ⟨⟨w, hwH⟩, hwl, rfl⟩)
  obtain ⟨κ, hκK, hκ⟩ := mem_modO2Image'.mp hwK
  have hq : ((κ⁻¹ * ⟨w, hwH⟩ : ↥H) : G) ∈ pCoreOf 2 H := by
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥H) (κ⁻¹ * ⟨w, hwH⟩) = 1 := by
      rw [map_mul, map_inv, hκ, inv_mul_cancel]
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← pCoreOf_subgroupOf',
      Subgroup.mem_subgroupOf] at h1
  obtain ⟨k', hk'⟩ : ∃ k : ℕ, ((κ⁻¹ * ⟨w, hwH⟩ : ↥H) : G) ^ 2 ^ k = 1 := by
    obtain ⟨k, hk⟩ := S.hyp.fsu.sylow.1 ⟨_, L32A.pCoreOf_le_of_le S.hyp hTH hq⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  set π' := QuotientGroup.mk' (K.subgroupOf H) with hπ'
  have hπ'w : π' ⟨w, hwH⟩ = 1 := by
    refine map_eq_one_of_odd π' hwo' (k := k') ?_
    have e : (⟨w, hwH⟩ : ↥H) = κ * (κ⁻¹ * ⟨w, hwH⟩) := (mul_inv_cancel_left κ _).symm
    have hκ1 : π' κ = 1 := (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hκK)
    rw [e, map_mul, hκ1, one_mul, ← map_pow]
    have : (κ⁻¹ * ⟨w, hwH⟩ : ↥H) ^ 2 ^ k' = 1 := Subtype.ext (by simpa using hk')
    rw [this, map_one]
  exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hπ'w)

section Psi

variable {V₂ : Subgroup G} [IsMulCommutative ↥V]

theorem l1_star_le_of_psi_eq (S : Setting147 G T L V H) (S14 : L32NSet14.Setting G T L V V₂)
    {ψ : ↥(L32NSet14.nX T V) →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)}
    (hψ : ∀ x, ψ x = 1 ↔ (x : G) ∈ L32NSet14.trivSub V (fsuV1 T V))
    {N : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)} (hN : N.Normal)
    {x : G} (hxX : x ∈ L32NSet14.nX T V) (hx1 : ψ ⟨x, hxX⟩ ≠ 1) (hx3 : ψ ⟨x, hxX⟩ ^ 3 = 1)
    {y : G} (hyL : y ∈ L) (hyX : y ∈ L32NSet14.nX T V) (hyH : y ∈ H)
    (hyN : QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, hyH⟩ ∈ N)
    (hψy : ψ ⟨y, hyX⟩ = ψ ⟨x, hxX⟩) : modO2Image H (l1 T L V) ≤ N := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH : T ≤ H := Setting147.TH' S
  have h2T : ∀ u ∈ T, ∃ k : ℕ, u ^ 2 ^ k = 1 := fun u hu => by
    obtain ⟨k, hk⟩ := S.hyp.fsu.sylow.1 ⟨u, hu⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have key : l1 T L V ≤ (N.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥H))).map H.subtype := by
    show Subgroup.closure _ ≤ _
    refine (Subgroup.closure_le _).mpr ?_
    rintro w ⟨⟨hwL, hwN⟩, hwo⟩
    have hwX : w ∈ L32NSet14.nX T V := ⟨S14.LV hwL, hwN⟩
    obtain ⟨j, hj⟩ : ∃ j : ℕ, ψ ⟨w, hwX⟩ = ψ ⟨y, hyX⟩ ^ j := by
      rcases sl2_trich (ψ ⟨x, hxX⟩) (ψ ⟨w, hwX⟩) hx1 hx3 with h | h | h | h
      · exact ⟨0, by rw [h, pow_zero]⟩
      · exact ⟨1, by rw [h, hψy, pow_one]⟩
      · exact ⟨2, by rw [h, hψy, pow_two]⟩
      · refine ⟨0, ?_⟩
        rw [pow_zero]
        have hwo' : Odd (orderOf (⟨w, hwX⟩ : ↥(L32NSet14.nX T V))) := by
          rwa [Subgroup.orderOf_mk]
        exact map_eq_one_of_odd ψ hwo' (k := 1) (by rw [pow_one]; exact h)
    have huX : w * (y ^ j)⁻¹ ∈ L32NSet14.nX T V := mul_mem hwX (inv_mem (pow_mem hyX j))
    have hut : w * (y ^ j)⁻¹ ∈ L32NSet14.trivSub V (fsuV1 T V) := by
      refine (hψ ⟨_, huX⟩).mp ?_
      have e : (⟨w * (y ^ j)⁻¹, huX⟩ : ↥(L32NSet14.nX T V)) =
          ⟨w, hwX⟩ * (⟨y, hyX⟩ ^ j)⁻¹ := Subtype.ext (by simp)
      rw [e, map_mul, map_inv, map_pow, hj, mul_inv_cancel]
    have huL : w * (y ^ j)⁻¹ ∈ L := mul_mem hwL (inv_mem (pow_mem hyL j))
    have huT : w * (y ^ j)⁻¹ ∈ T := pCoreOf_L_nX_le_T S.hyp S14
      (S14.le_pCoreOf inf_le_right (inf_le_left.trans le_sup_left) ⟨⟨huL, huX⟩, hut⟩)
    have hwH : w ∈ H := by
      rw [← inv_mul_cancel_right w (y ^ j)]
      exact mul_mem (hTH huT) (pow_mem hyH j)
    have hwo' : Odd (orderOf (⟨w, hwH⟩ : ↥H)) := by rwa [Subgroup.orderOf_mk]
    set π := (QuotientGroup.mk' N).comp (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) with hπ
    have hπy : π ⟨y, hyH⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr hyN
    obtain ⟨k, hk⟩ := h2T _ huT
    have hπw : π ⟨w, hwH⟩ = 1 := by
      have e : (⟨w, hwH⟩ : ↥H) = ⟨w * (y ^ j)⁻¹, hTH huT⟩ * ⟨y, hyH⟩ ^ j :=
        Subtype.ext (by simp)
      refine map_eq_one_of_odd π hwo' (k := k) ?_
      rw [e, map_mul, map_pow, hπy, one_pow, mul_one, ← map_pow]
      have : (⟨w * (y ^ j)⁻¹, hTH huT⟩ : ↥H) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk)
      rw [this, map_one]
    exact ⟨⟨w, hwH⟩, (QuotientGroup.eq_one_iff
      (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨w, hwH⟩)).mp hπw, rfl⟩
  intro z hz
  obtain ⟨w, hw, rfl⟩ := mem_modO2Image'.mp hz
  obtain ⟨w', hw', hww⟩ := Subgroup.mem_map.mp (key hw)
  have : w' = w := Subtype.ext hww
  rw [← this]
  exact hw'

theorem l1_le_of_psi_eq (S : Setting147 G T L V H) (S14 : L32NSet14.Setting G T L V V₂)
    {ψ : ↥(L32NSet14.nX T V) →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)}
    (hψ : ∀ x, ψ x = 1 ↔ (x : G) ∈ L32NSet14.trivSub V (fsuV1 T V))
    {K : Subgroup G} (hK : K ∈ cComp H) (hKn : H ≤ Subgroup.normalizer (K : Set G))
    {x : G} (hxX : x ∈ L32NSet14.nX T V) (hx1 : ψ ⟨x, hxX⟩ ≠ 1) (hx3 : ψ ⟨x, hxX⟩ ^ 3 = 1)
    {y : G} (hyL : y ∈ L) (hyX : y ∈ L32NSet14.nX T V) (hyH : y ∈ H)
    (hyK : QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, hyH⟩ ∈ modO2Image H K)
    (hψy : ψ ⟨y, hyX⟩ = ψ ⟨x, hxX⟩) : l1 T L V ≤ K := by
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hKs : (K.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hKn
  have hKbN : (modO2Image H K).Normal :=
    Subgroup.Normal.map hKs _ (QuotientGroup.mk'_surjective _)
  exact l1_le_of_star_le S hK hKn
    (l1_star_le_of_psi_eq S S14 hψ hKbN hxX hx1 hx3 hyL hyX hyH hyK hψy)

omit [Finite G] [IsMulCommutative ↥V] in
theorem comm_mem_L_nX {s β : G} (hsL : s ∈ L) (hsX : s ∈ L32NSet14.nX T V)
    (hβX : β ∈ L32NSet14.nX T V) (hβL : β ∈ Subgroup.normalizer (L : Set G)) :
    s * β * s⁻¹ * β⁻¹ ∈ L ∧ s * β * s⁻¹ * β⁻¹ ∈ L32NSet14.nX T V := by
  refine ⟨?_, mul_mem (mul_mem (mul_mem hsX hβX) (inv_mem hsX)) (inv_mem hβX)⟩
  have h1 : β * s⁻¹ * β⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hβL _).mp (inv_mem hsL)
  have e : s * β * s⁻¹ * β⁻¹ = s * (β * s⁻¹ * β⁻¹) := by group
  rw [e]
  exact mul_mem hsL h1

theorem psi_eq_one_of_mem (S : Setting147 G T L V H) (S14 : L32NSet14.Setting G T L V V₂)
    {ψ : ↥(L32NSet14.nX T V) →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)}
    (hψ : ∀ x, ψ x = 1 ↔ (x : G) ∈ L32NSet14.trivSub V (fsuV1 T V))
    {K : Subgroup G} (hK : K ∈ cComp H) (hKn : H ≤ Subgroup.normalizer (K : Set G))
    (hl1K : ¬ l1 T L V ≤ K)
    {x : G} (hxL : x ∈ L) (hxX : x ∈ L32NSet14.nX T V) (hxH : x ∈ H) (hx1 : ψ ⟨x, hxX⟩ ≠ 1)
    (hx3 : ψ ⟨x, hxX⟩ ^ 3 = 1)
    {t : G} (htL : t ∈ L) (htX : t ∈ L32NSet14.nX T V) (htH : t ∈ H) (ht1 : ψ ⟨t, htX⟩ ≠ 1)
    (ht2 : ψ ⟨t, htX⟩ ^ 2 = 1)
    {β : G} (hβX : β ∈ L32NSet14.nX T V) (hβL : β ∈ Subgroup.normalizer (L : Set G))
    (hβH : β ∈ H) (hβK : QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨β, hβH⟩ ∈ modO2Image H K) :
    ψ ⟨β, hβX⟩ = 1 := by
  by_contra hβ1
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hKs : (K.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hKn
  have hKbN : (modO2Image H K).Normal :=
    Subgroup.Normal.map hKs _ (QuotientGroup.mk'_surjective _)
  set a := ψ ⟨x, hxX⟩ with ha
  have ha4 : a * a * (a * a) = a := by
    calc a * a * (a * a) = a ^ 3 * a := by rw [pow_three]; simp only [mul_assoc]
      _ = a := by rw [hx3, one_mul]
  have key : ∀ s (hsL : s ∈ L) (hsX : s ∈ L32NSet14.nX T V) (hsH : s ∈ H),
      ψ ⟨s, hsX⟩ * ψ ⟨β, hβX⟩ * (ψ ⟨s, hsX⟩)⁻¹ * (ψ ⟨β, hβX⟩)⁻¹ = a ∨
        ψ ⟨s, hsX⟩ * ψ ⟨β, hβX⟩ * (ψ ⟨s, hsX⟩)⁻¹ * (ψ ⟨β, hβX⟩)⁻¹ = a * a → False := by
    intro s hsL hsX hsH hcase
    obtain ⟨hcL, hcX⟩ := comm_mem_L_nX hsL hsX hβX hβL
    have hcH : s * β * s⁻¹ * β⁻¹ ∈ H := mul_mem (mul_mem (mul_mem hsH hβH) (inv_mem hsH))
      (inv_mem hβH)
    have hcK : QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨_, hcH⟩ ∈ modO2Image H K := by
      have e : (⟨s * β * s⁻¹ * β⁻¹, hcH⟩ : ↥H) =
          ⟨s, hsH⟩ * ⟨β, hβH⟩ * ⟨s, hsH⟩⁻¹ * ⟨β, hβH⟩⁻¹ := rfl
      rw [e]
      simp only [map_mul, map_inv]
      exact mul_mem (hKbN.conj_mem _ hβK _) (inv_mem hβK)
    have hψc : ψ ⟨_, hcX⟩ =
        ψ ⟨s, hsX⟩ * ψ ⟨β, hβX⟩ * (ψ ⟨s, hsX⟩)⁻¹ * (ψ ⟨β, hβX⟩)⁻¹ := by
      have e : (⟨s * β * s⁻¹ * β⁻¹, hcX⟩ : ↥(L32NSet14.nX T V)) =
          ⟨s, hsX⟩ * ⟨β, hβX⟩ * ⟨s, hsX⟩⁻¹ * ⟨β, hβX⟩⁻¹ := rfl
      rw [e]
      simp only [map_mul, map_inv]
    rcases hcase with h | h
    · exact hl1K (l1_le_of_psi_eq S S14 hψ hK hKn hxX hx1 hx3 hcL hcX hcH hcK (hψc.trans h))
    · have hcX2 := mul_mem hcX hcX
      have hcK2 : QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨_, mul_mem hcH hcH⟩ ∈ modO2Image H K := by
        have e : (⟨(s * β * s⁻¹ * β⁻¹) * (s * β * s⁻¹ * β⁻¹), mul_mem hcH hcH⟩ : ↥H) =
            ⟨_, hcH⟩ * ⟨_, hcH⟩ := rfl
        rw [e, map_mul]
        exact mul_mem hcK hcK
      refine hl1K (l1_le_of_psi_eq S S14 hψ hK hKn hxX hx1 hx3 (mul_mem hcL hcL) hcX2
        (mul_mem hcH hcH) hcK2 ?_)
      have e : (⟨(s * β * s⁻¹ * β⁻¹) * (s * β * s⁻¹ * β⁻¹), hcX2⟩ : ↥(L32NSet14.nX T V)) =
          ⟨_, hcX⟩ * ⟨_, hcX⟩ := rfl
      rw [e, map_mul, hψc, h, ha4]
  rcases sl2_comm' a (ψ ⟨t, htX⟩) (ψ ⟨β, hβX⟩) hx1 hx3 ht1 ht2 hβ1 with h | h | h | h
  · exact key t htL htX htH (Or.inl h)
  · exact key t htL htX htH (Or.inr h)
  · exact key x hxL hxX hxH (Or.inl h)
  · exact key x hxL hxX hxH (Or.inr h)

theorem comm_mem_szS1_of_psi (S : Setting147 G T L V H) (S14 : L32NSet14.Setting G T L V V₂)
    {ψ : ↥(L32NSet14.nX T V) →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)}
    (hψ : ∀ x, ψ x = 1 ↔ (x : G) ∈ L32NSet14.trivSub V (fsuV1 T V))
    {K : Subgroup G} (hK : K ∈ cComp H) (hKn : H ≤ Subgroup.normalizer (K : Set G))
    {s : G} (hsL : s ∈ L) (hsX : s ∈ L32NSet14.nX T V) (hsH : s ∈ H)
    {β : G} (hβX : β ∈ L32NSet14.nX T V) (hβL : β ∈ Subgroup.normalizer (L : Set G))
    (hβH : β ∈ H) (hβK : QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨β, hβH⟩ ∈ modO2Image H K)
    (hψβ : ψ ⟨β, hβX⟩ = 1) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥H) (⟨s, hsH⟩ * ⟨β, hβH⟩ * ⟨s, hsH⟩⁻¹ * ⟨β, hβH⟩⁻¹) ∈
      szS1 T H K := by
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hKs : (K.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hKn
  have hKbN : (modO2Image H K).Normal :=
    Subgroup.Normal.map hKs _ (QuotientGroup.mk'_surjective _)
  obtain ⟨hcL, hcX⟩ := comm_mem_L_nX hsL hsX hβX hβL
  have hct : s * β * s⁻¹ * β⁻¹ ∈ L32NSet14.trivSub V (fsuV1 T V) := by
    refine (hψ ⟨_, hcX⟩).mp ?_
    have e : (⟨s * β * s⁻¹ * β⁻¹, hcX⟩ : ↥(L32NSet14.nX T V)) =
        ⟨s, hsX⟩ * ⟨β, hβX⟩ * ⟨s, hsX⟩⁻¹ * ⟨β, hβX⟩⁻¹ := rfl
    rw [e]
    simp only [map_mul, map_inv, hψβ, mul_one, inv_one, mul_inv_cancel]
  have hcT : s * β * s⁻¹ * β⁻¹ ∈ T := pCoreOf_L_nX_le_T S.hyp S14
    (S14.le_pCoreOf inf_le_right (inf_le_left.trans le_sup_left) ⟨⟨hcL, hcX⟩, hct⟩)
  refine Subgroup.mem_inf.mpr ⟨mem_modO2Image'.mpr ⟨_, hcT, rfl⟩, ?_⟩
  simp only [map_mul, map_inv]
  exact mul_mem (hKbN.conj_mem _ hβK _) (inv_mem hβK)

end Psi

end CFSG.Quasithin.H13.L32A.C
