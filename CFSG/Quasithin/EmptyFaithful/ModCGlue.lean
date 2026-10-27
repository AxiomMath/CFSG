module

public import CFSG.Quasithin.EmptyFaithful.ModCOutX
public import CFSG.Quasithin.EmptyFaithful.ModCCosets
public import CFSG.Quasithin.EmptyFaithful.ModCPhi
public import CFSG.Quasithin.EmptyFaithful.ModBR4G

public section

namespace CFSG.Quasithin.ModC

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Quasithin CFSG.Quasithin.G6
open scoped commutatorElement IsMulCommutative

variable {G : Type} [Group G] [Finite G]

theorem card_eq_of_s3 {I₂ : Subgroup G} (hs3 : Nonempty (OTwoQuot I₂ ≃* Equiv.Perm (Fin 3))) :
    ∃ b : ℕ, Nat.card ↥I₂ = 6 * 2 ^ b := by
  obtain ⟨e⟩ := hs3
  have hq : Nat.card (OTwoQuot I₂) = 6 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have hpc : IsPGroup 2 ↥(CFSG.Open.pCore 2 ↥I₂) :=
    CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥I₂) 2
  obtain ⟨b, hb⟩ := hpc.exists_card_eq
  refine ⟨b, ?_⟩
  have := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.Open.pCore 2 ↥I₂)
  rw [hb] at this
  have hq' : Nat.card (↥I₂ ⧸ CFSG.Open.pCore 2 ↥I₂) = 6 := hq
  rw [hq'] at this
  exact this

theorem out_of_module {n : ℕ} (hn : 3 ≤ n) (hmodel : ModelOut n) {o : ℕ} (ho : Odd o)
    (hcardA : Nat.card (alternatingGroup (Fin n)) = 8 * o)
    {T M H : Subgroup G} {u : G} {I I₂ K : Subgroup G}
    (c : Facts14610 T M H u I I₂) (hK : Concl14610List T M I I₂ K) (hsyl : IsSylowTwoOf (T ⊓ I) I)
    (hLT : yOfL22 T M ⊔ T = i1Of1469 T M I ⊔ pCoreOf 2 (yOfL22 T M ⊔ T))
    (hshort : IsShort2 K) (Φ : ↥(blockU K) ≃* ↥(coreMod n))
    (hΦ : ∀ g : MulAut ↥(blockU K), g ∈ autOn K (blockU K) ↔
      ∃ σ ∈ alternatingGroup (Fin n), ∀ w, Φ (g w) = coreAct n σ (Φ w))
    (hTu : T ⊓ I = tU T u) (hne : Nat.card (conjClosure (VZ T M) I₂) ≠ 2 ^ 3)
    (huW : u ∉ blockU K) : False := by
  classical
  have S : Setting146 G T M := c.setting
  have hVW : VZ T M ≤ blockU K := (ModB.wOf1469_eq_blockU_of_short hshort) ▸ hK.v_le_w
  have hI₂I : I₂ ≤ I := c.gen ▸ le_sup_right
  have hTI₂ : T ⊓ I ≤ I₂ := c.le_I₂
  have hcommW := isMulCommutative_blockU hshort
  have hsqW : ∀ w : ↥(blockU K), w ^ 2 = 1 := fun w => Subtype.ext (hshort.2.2.1.2 w w.2)
  have hKW : K ≤ Subgroup.normalizer (blockU K : Set G) := C1.le_normalizer_blockU K
  have hIW : I ≤ Subgroup.normalizer (blockU K : Set G) := fun g hg =>
    C1.mem_normalizer_blockU (hK.normal hg)
  let β : ↥I →* MulAut ↥(blockU K) := A4.actionOn (blockU K) I hIW
  have hβ : ∀ (g : ↥I) (w : ↥(blockU K)), ((β g w : ↥(blockU K)) : G) = (g : G) * w * (g : G)⁻¹ :=
    fun g w => rfl
  let K'' : Subgroup ↥I := K.subgroupOf I
  let T'' : Subgroup ↥I := (T ⊓ I).subgroupOf I
  let I₂'' : Subgroup ↥I := I₂.subgroupOf I
  have hK''N : K''.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hK.le).2 hK.normal
  have hKT : K'' ⊔ T'' = ⊤ := by
    have h1 : K ⊔ (T ⊓ I) = I := hK.eq_sup.symm
    rw [← Subgroup.subgroupOf_sup hK.le inf_le_right, h1, Subgroup.subgroupOf_self]
  have hKb : autOn K (blockU K) = K''.map β := by
    ext a
    rw [A4.mem_autOn_iff hKW, Subgroup.mem_map]
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨⟨(k : G), hK.le k.2⟩, k.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨(y : G), hy⟩, rfl⟩
  have hΘ : ∀ σ w, Φ (liftAut Φ σ w) = coreAct n σ (Φ w) := liftAut_apply Φ
  have hΘinj : Function.Injective (liftAut Φ) := theta_injective hn Φ hΘ
  have hKbΘ : K''.map β = (alternatingGroup (Fin n)).map (liftAut Φ) := by
    rw [← hKb]
    ext g
    rw [Subgroup.mem_map]
    constructor
    · intro hg
      obtain ⟨σ, hσ, hσg⟩ := (hΦ g).mp hg
      refine ⟨σ, hσ, MulEquiv.ext fun w => Φ.injective ?_⟩
      rw [hΘ, hσg w]
    · rintro ⟨σ, hσ, rfl⟩
      exact (hΦ _).mpr ⟨σ, hσ, hΘ σ⟩
  have hcardKb : Nat.card ↥(K''.map β) = 8 * o := by
    rw [hKbΘ, Subgroup.card_map_of_injective hΘinj, hcardA]
  have hT2 : IsPGroup 2 ↥T'' := hsyl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hsyl.1).symm
  have hTi : ¬ 2 ∣ T''.index := hsyl.2.2
  have h8 := ModB.card_inf_map_ge β K'' T'' hKT hT2 hTi ho hcardKb
  have hB2 : IsPGroup 2 ↥(T''.map β) := hT2.map β
  have hnorm : ∀ τ ∈ T''.map β, ∀ k ∈ K''.map β, τ * k * τ⁻¹ ∈ K''.map β := by
    intro τ hτ k hk
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hτ
    obtain ⟨k₀, hk₀, rfl⟩ := Subgroup.mem_map.mp hk
    refine Subgroup.mem_map.mpr ⟨t * k₀ * t⁻¹, hK''N.conj_mem k₀ hk₀ t, ?_⟩
    simp
  have hTM : T ≤ M := S.hyp1281.inM.2
  have hMV : M ≤ Subgroup.normalizer (VZ T M : Set G) := le_normalizer_conjClosure _ _
  have hy : ∃ y ∈ yOfL22 T M ⊓ I, Odd (orderOf y) ∧ y ∉ mcOf T := by
    by_contra hcon
    push Not at hcon
    exact S.not_lI_le_mcOf hLT ((Subgroup.closure_le _).mpr fun y hy => hcon y hy.1 hy.2)
  obtain ⟨y, hyLI, hyodd, hyG⟩ := hy
  obtain ⟨z, hzZ, hzy⟩ : ∃ z ∈ quasithinOmegaOneCenter T, ¬ (z * y = y * z) := by
    by_contra hno
    push Not at hno
    exact hyG (Subgroup.mem_centralizer_iff.mpr hno)
  have hzV : z ∈ VZ T M := le_conjClosure _ _ hzZ
  have hz1 : z ≠ 1 := by
    rintro rfl
    exact hzy (by simp)
  have hyI : y ∈ I := hyLI.2
  have hyM : y ∈ M := S.hyp1281.le hyLI.1
  have hyK : y ∈ K := by
    rw [hK.eq_residual]
    exact mem_oTwoUpper_of_odd hyI hyodd
  have hvV : y * z * y⁻¹ ∈ VZ T M := (Subgroup.mem_normalizer_iff.mp (hMV hyM) z).mp hzV
  set z' : ↥(blockU K) := ⟨z, hVW hzV⟩ with hz'
  set v' : ↥(blockU K) := ⟨y * z * y⁻¹, hVW hvV⟩ with hv'
  have hz'1 : z' ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have hv'1 : v' ≠ 1 := by
    intro h
    apply hz1
    have h1 : y * z * y⁻¹ = 1 := congrArg Subtype.val h
    calc z = y⁻¹ * (y * z * y⁻¹) * y := by group
      _ = 1 := by rw [h1]; group
  have hv'z' : v' ≠ z' := by
    intro h
    apply hzy
    have h1 : y * z * y⁻¹ = z := congrArg Subtype.val h
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  let V' : Subgroup ↥(blockU K) := (VZ T M).subgroupOf (blockU K)
  have hz'V : z' ∈ V' := hzV
  have hv'V : v' ∈ V' := hvV
  have hV4 : Nat.card ↥V' = 4 := by
    have : Nat.card ↥V' = Nat.card ↥(VZ T M) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVW).toEquiv
    rw [this]
    exact S.hyp.rank_two
  have hz'sq : z' * z' = 1 := by rw [← pow_two]; exact hsqW z'
  have hV : ∀ a ∈ V', a = 1 ∨ a = z' ∨ a = v' ∨ a = z' * v' := by
    intro a ha
    have hzv : z' * v' ∈ V' := V'.mul_mem hz'V hv'V
    have hd1 : z' * v' ≠ 1 := by
      intro h
      apply hv'z'
      have : v' = z'⁻¹ := eq_inv_of_mul_eq_one_right h
      rw [this]
      exact inv_eq_of_mul_eq_one_right hz'sq
    have hdz : z' * v' ≠ z' := fun h => hv'1 (mul_eq_left.mp h)
    have hdv : z' * v' ≠ v' := fun h => hz'1 (mul_eq_right.mp h)
    rcases eq_or_eq_or_eq_or_eq_of_card_four hV4 (a := (1 : ↥V')) (b := ⟨z', hz'V⟩) (c := ⟨v', hv'V⟩)
      (d := ⟨z' * v', hzv⟩) (fun he => hz'1 (congrArg Subtype.val he).symm)
      (fun he => hv'1 (congrArg Subtype.val he).symm) (fun he => hd1 (congrArg Subtype.val he).symm)
      (fun he => hv'z' (congrArg Subtype.val he).symm) (fun he => hdz (congrArg Subtype.val he).symm)
      (fun he => hdv (congrArg Subtype.val he).symm) ⟨a, ha⟩ with h | h | h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (Or.inl (congrArg Subtype.val h))
    · exact Or.inr (Or.inr (Or.inl (congrArg Subtype.val h)))
    · exact Or.inr (Or.inr (Or.inr (congrArg Subtype.val h)))
  have hBz : ∀ τ ∈ T''.map β, τ z' = z' := by
    intro τ hτ
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hτ
    have htT : (t : G) ∈ T := ((ht : (t : G) ∈ T ⊓ I)).1
    have h1 := S146T.comm_Z_T htT hzZ
    apply Subtype.ext
    rw [hβ]
    show (t : G) * z * (t : G)⁻¹ = z
    calc (t : G) * z * (t : G)⁻¹ = ((t : G) * z) * (t : G)⁻¹ := rfl
      _ = (z * (t : G)) * (t : G)⁻¹ := by rw [h1]
      _ = z := by group
  have hBV : ∀ τ ∈ T''.map β, ∀ a ∈ V', τ a ∈ V' := by
    intro τ hτ a ha
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hτ
    have htT : (t : G) ∈ T := ((ht : (t : G) ∈ T ⊓ I)).1
    have ha' : (a : G) ∈ VZ T M := ha
    show ((β t a : ↥(blockU K)) : G) ∈ VZ T M
    rw [hβ]
    exact (Subgroup.mem_normalizer_iff.mp (hMV (hTM htT)) (a : G)).mp ha'
  have hwt : ∃ k ∈ K''.map β, k z' = v' :=
    ⟨β ⟨y, hyI⟩, Subgroup.mem_map.mpr ⟨⟨y, hyI⟩, hyK, rfl⟩, Subtype.ext rfl⟩
  obtain ⟨b, hb⟩ := card_eq_of_s3 c.s3
  have h3 : 3 ∣ Nat.card ↥I₂ := ⟨2 * 2 ^ b, by rw [hb]; ring⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g₀, hg₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥I₂) 3 h3
  set g : G := (g₀ : G) with hgdef
  have hgI₂ : g ∈ I₂ := g₀.2
  have hgI : g ∈ I := hI₂I hgI₂
  have hgord : orderOf g = 3 := by rw [hgdef, Subgroup.orderOf_coe, hg₀]
  have hg3 : g ^ 3 = 1 := by rw [← hgord]; exact pow_orderOf_eq_one g
  have hg1 : g ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hgord
    omega
  have hgK : g ∈ K := by
    rw [hK.eq_residual]
    exact mem_oTwoUpper_of_odd hgI (by rw [hgord]; exact ⟨1, rfl⟩)
  have hidx : (T ⊓ I).relIndex I₂ ∣ 3 := ModB.relIndex_dvd_three_of_sylow hsyl hTI₂ hI₂I c.s3
  have hcos := coset_decomp hidx hsyl.2.1 hgI₂ hg3 hg1
  have hI1M : i1Of1469 T M I ≤ M := by
    refine sup_le ?_ (inf_le_left.trans hTM)
    exact ((oTwoUpper_le _).trans inf_le_left).trans S.hyp1281.le
  have hgM : g ∉ M := by
    intro hgM
    apply c.hI.1.2.2
    have hI₂M : I₂ ≤ M := by
      intro x hx
      rcases hcos x hx with h | h | h
      · exact hTM (h.1)
      · have := M.mul_mem hgM (hTM h.1)
        simpa using this
      · have := M.mul_mem (M.inv_mem hgM) (hTM h.1)
        simpa using this
    rw [c.gen]
    exact sup_le hI1M hI₂M
  have hgz : ∀ x ∈ quasithinOmegaOneCenter T, g * x * g⁻¹ = x := by
    intro x hx
    have hH : H ≤ mcOf T := S.le_mcOf c.hH
    have hg' : g ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := hH (c.I₂_le hgI₂)
    have h1 := (Subgroup.mem_centralizer_iff.mp hg') x hx
    calc g * x * g⁻¹ = (g * x) * g⁻¹ := rfl
      _ = (x * g) * g⁻¹ := by rw [h1]
      _ = x := by group
  let g' : ↥I := ⟨g, hgI⟩
  have hgz' : β g' z' = z' := Subtype.ext (by rw [hβ]; exact hgz z hzZ)
  have hgM' : ¬ (β g' v' = v' ∨ β g' v' = z' * v') := by
    intro hcase
    apply hgM
    have hmapsV : ∀ a₁ ∈ V', β g' a₁ ∈ V' := by
      intro a₁ h₁
      rcases hV a₁ h₁ with rfl | rfl | rfl | rfl
      · rw [map_one]
        exact V'.one_mem
      · rw [hgz']
        exact hz'V
      · rcases hcase with h | h
        · rw [h]
          exact hv'V
        · rw [h]
          exact V'.mul_mem hz'V hv'V
      · rw [map_mul, hgz']
        rcases hcase with h | h
        · rw [h]
          exact V'.mul_mem hz'V hv'V
        · rw [h]
          exact V'.mul_mem hz'V (V'.mul_mem hz'V hv'V)
    have hnormg : g ∈ Subgroup.normalizer (VZ T M : Set G) := by
      refine mem_normalizer_of_conj_le hg3 fun a ha => ?_
      have := hmapsV ⟨a, hVW ha⟩ ha
      exact this
    rw [S.hyp1281.normalizer_VZ] at hnormg
    exact hnormg
  have hgK'' : g' ∈ K'' := hgK
  have hT₀V : ∀ t ∈ T ⊓ I, ∀ a ∈ VZ T M, t * a * t⁻¹ ∈ VZ T M := fun t ht a ha =>
    (Subgroup.mem_normalizer_iff.mp (hMV (hTM ht.1)) a).mp ha
  have hjoin : conjClosure (VZ T M) I₂ = (join3 V' (β g')).map (blockU K).subtype :=
    conjClosure_eq_join3 hVW hI₂I hT₀V hgI₂ hg3 hcos β hβ
  have hne' : Nat.card ↥(join3 V' (β g')) ≠ 8 := by
    intro h8'
    apply hne
    rw [hjoin, Subgroup.card_map_of_injective (blockU K).subtype_injective, h8']
    norm_num
  have hBB₂ : T''.map β ≤ I₂''.map β := Subgroup.map_mono fun t ht => (hTI₂ ht : (t : G) ∈ I₂)
  have hgB₂ : β g' ∈ I₂''.map β := Subgroup.mem_map.mpr ⟨g', hgI₂, rfl⟩
  have h5 : ¬ 5 ∣ Nat.card ↥(I₂''.map β) := by
    intro h5d
    have h1 : Nat.card ↥(I₂''.map β) ∣ Nat.card ↥I₂'' := Subgroup.card_map_dvd _ _
    have h2 : Nat.card ↥I₂'' = Nat.card ↥I₂ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hI₂I).toEquiv
    have h3' := h5d.trans h1
    rw [h2, hb] at h3'
    have hp : Nat.Prime 5 := by norm_num
    rcases (Nat.Prime.dvd_mul hp).mp h3' with h | h
    · omega
    · have := Nat.Prime.dvd_of_dvd_pow hp h
      omega
  obtain ⟨x, hxjoin, hx1, hxfix, ⟨j, hjK, hjx, hjz⟩, ⟨j', hj'K, hj'x, hj'v⟩⟩ :=
    abstractOut hn hmodel ho hcardA Φ hΘ hKbΘ hB2 hnorm h8 hz'1 hv'1 hv'z' hz'V hv'V hV hBz hBV hwt
      (Subgroup.mem_map.mpr ⟨g', hgK'', rfl⟩)
      (by rw [← map_pow, show g' ^ 3 = 1 from Subtype.ext hg3, map_one]) hgz' (fun h => hgM' (Or.inl h)) (fun h => hgM' (Or.inr h)) hne' hBB₂ hgB₂ h5
  have hxmem : (x : G) ∈ conjClosure (VZ T M) I₂ := by
    rw [hjoin]
    exact Subgroup.mem_map.mpr ⟨x, hxjoin, rfl⟩
  have hxU : (x : G) ∈ conjClosure (VZ T M) H := conjClosure_mono le_rfl c.I₂_le hxmem
  have hx1' : (x : G) ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hxu : (x : G) * u ≠ 1 := by
    intro h
    apply huW
    have : u = (x : G)⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this]
    exact (blockU K).inv_mem x.2
  have hxT : ∀ t ∈ tU T u, t * (x : G) * t⁻¹ = x := by
    intro t ht
    rw [← hTu] at ht
    have hτ : β ⟨t, ht.2⟩ ∈ T''.map β := Subgroup.mem_map.mpr ⟨⟨t, ht.2⟩, ht, rfl⟩
    have := congrArg Subtype.val (hxfix _ hτ)
    rw [hβ] at this
    exact this
  have hJx : ∀ k ∈ K ⊓ Subgroup.centralizer ({(x : G)} : Set G), k * (x : G) * k⁻¹ = x := by
    intro k hk
    have h := Subgroup.mem_centralizer_iff.mp hk.2 (x : G) rfl
    calc k * (x : G) * k⁻¹ = (k * x) * k⁻¹ := rfl
      _ = (x * k) * k⁻¹ := by rw [h]
      _ = x := by group
  have hmemJ : ∀ k : ↥I, k ∈ K'' → β k x = x →
      (k : G) ∈ K ⊓ Subgroup.centralizer ({(x : G)} : Set G) := by
    intro k hk hkx
    have hkx' : (k : G) * (x : G) * (k : G)⁻¹ = x := by
      have := congrArg Subtype.val hkx
      rw [hβ] at this
      exact this
    refine ⟨hk, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩
    rw [Set.mem_singleton_iff.mp hh]
    calc (x : G) * k = ((k : G) * x * (k : G)⁻¹) * k := by rw [hkx']
      _ = k * x := by group
  have hJM : ¬ K ⊓ Subgroup.centralizer ({(x : G)} : Set G) ≤ M := by
    intro hJM
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hj'K
    have hkM := hJM (hmemJ k hk hj'x)
    apply hj'v
    show ((β k v' : ↥(blockU K)) : G) ∈ VZ T M
    rw [hβ]
    exact (Subgroup.mem_normalizer_iff.mp (hMV hkM) (v' : G)).mp hvV
  have hJG : ¬ K ⊓ Subgroup.centralizer ({(x : G)} : Set G) ≤ mcOf T := by
    intro hJG
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hjK
    have hkG := hJG (hmemJ k hk hjx)
    apply hjz
    apply Subtype.ext
    rw [hβ]
    show (k : G) * z * (k : G)⁻¹ = z
    have h1 := (Subgroup.mem_centralizer_iff.mp hkG) z hzZ
    calc (k : G) * z * (k : G)⁻¹ = ((k : G) * z) * (k : G)⁻¹ := rfl
      _ = (z * (k : G)) * (k : G)⁻¹ := by rw [h1]
      _ = z := by group
  exact out_contradiction c hTu hxU hx1' hxu hxT (inf_le_left.trans hK.le) hJx hJM hJG

end CFSG.Quasithin.ModC
