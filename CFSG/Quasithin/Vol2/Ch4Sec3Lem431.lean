module

public import CFSG.Quasithin.Vol2.Ch4Sec1Lem412
public import CFSG.Quasithin.Vol2.Ch5Sec1Basic
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C5Rank1
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239ListedBasic
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Vol2.Ch1Unique
public import CFSG.Quasithin.Background.G2
public import CFSG.Quasithin.Vol2.Ch1Faithful

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open scoped Pointwise

@[expose] def LemmaC53C56Six : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H M₀ R TH : Subgroup G), HypC51 H M₀ R TH → R ≠ ⊥ →
    C5.NoCommonNormal R H M₀ → IsSylowTwoOf TH M₀ →
      ∃ K₁ K₂ : Subgroup G, K₁ ≠ K₂ ∧ IsBlock2 H K₁ ∧ IsBlock2 H K₂ ∧
        ((∃ m : ℕ, IsLin2Type K₁ m) ∨ IsAltType K₁ 3 ∨ IsAltType K₁ 5) ∧
        (∃ t ∈ TH, K₁.map (MulAut.conj t).toMonoidHom = K₂) ∧ oTwoUpper H = K₁ ⊔ K₂

variable {G : Type} [Group G] [Finite G]

theorem isSylowTwoOf_map_conj' {S H : Subgroup G} (hS : IsSylowTwoOf S H) (g : G) :
    IsSylowTwoOf (S.map (MulAut.conj g).toMonoidHom) (H.map (MulAut.conj g).toMonoidHom) := by
  rw [isSylowTwoOf_iff_maximal] at hS ⊢
  obtain ⟨hSH, hS2, hmax⟩ := hS
  refine ⟨map_conj_mono hSH g, hS2.map _, fun P hPH hP2 hSP => ?_⟩
  have h1 : S ≤ P.map (MulAut.conj g⁻¹).toMonoidHom := by
    have := map_conj_mono hSP g⁻¹
    rwa [map_conj_inv_map_conj] at this
  have h2 : P.map (MulAut.conj g⁻¹).toMonoidHom ≤ H := by
    have := map_conj_mono hPH g⁻¹
    rwa [map_conj_inv_map_conj] at this
  have h3 := map_conj_mono (hmax _ h2 (hP2.map _) h1) g
  rwa [map_conj_map_conj_inv] at h3

theorem isSylowTwoOf_sup_of_inf {L S : Subgroup G} (hS2 : IsPGroup 2 S)
    (hSL : S ≤ Subgroup.normalizer (L : Set G)) (hSyl : IsSylowTwoOf (S ⊓ L) L) :
    IsSylowTwoOf S (L ⊔ S) := by
  refine isSylowTwoOf_iff_maximal.mpr ⟨le_sup_right, hS2, fun P hP hP2 hSP x hx => ?_⟩
  have hx' : x ∈ ((L : Set G) * (S : Set G)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left L S hSL]
    exact hP hx
  obtain ⟨l, hl, s, hs, rfl⟩ := hx'
  have hlP : l ∈ P := by
    have := P.mul_mem hx (P.inv_mem (hSP hs))
    simpa using this
  have hlS : l ∈ S ⊓ L :=
    (isSylowTwoOf_iff_maximal.mp hSyl).2.2 (P ⊓ L) inf_le_right (hP2.to_le inf_le_left)
      (inf_le_inf_right L hSP) ⟨hlP, hl⟩
  exact S.mul_mem hlS.1 hs

omit [Finite G] in
theorem le_inf_sup_of_le_normalizer {L S X : Subgroup G}
    (hSL : S ≤ Subgroup.normalizer (L : Set G)) (hSX : S ≤ X) (hX : X ≤ L ⊔ S) :
    X ≤ (X ⊓ L) ⊔ S := by
  intro x hx
  have hx' : x ∈ ((L : Set G) * (S : Set G)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left L S hSL]
    exact hX hx
  obtain ⟨l, hl, s, hs, rfl⟩ := hx'
  have hlX : l ∈ X := by
    have := X.mul_mem hx (X.inv_mem (hSX hs))
    simpa using this
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨hlX, hl⟩) (Subgroup.mem_sup_right hs)

omit [Finite G] in
theorem le_normalizer_borel {L S : Subgroup G} (hSL : S ≤ Subgroup.normalizer (L : Set G)) :
    S ≤ Subgroup.normalizer
      ((L ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) : Subgroup G) : Set G) := by
  intro s hs
  have hsSL : s ∈ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) :=
    mem_normalizer_inf (Subgroup.le_normalizer hs) (hSL hs)
  exact mem_normalizer_inf (hSL hs) (Subgroup.le_normalizer hsSL)

omit [Finite G] in
theorem isUniqueMaxOver_sup {L S : Subgroup G} (hSL : S ≤ Subgroup.normalizer (L : Set G))
    (hR : RankOneAt L (S ⊓ L)) :
    IsUniqueMaxOver (L ⊔ S)
      S ((L ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G)) ⊔ S) := by
  set B := L ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) with hB
  have hSB : S ≤ Subgroup.normalizer (B : Set G) := le_normalizer_borel hSL
  have hkey : ∀ X : Subgroup G, S ≤ X → X ≤ L ⊔ S → X ≠ L ⊔ S → X ≤ B ⊔ S := by
    intro X hSX hX hne
    have hXL : X ⊓ L ≠ L := by
      intro heq
      apply hne
      exact le_antisymm hX (_root_.sup_le (heq ▸ inf_le_left) hSX)
    have hle : X ⊓ L ≤ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) :=
      hR.unique_max (X ⊓ L) (inf_le_inf_right L hSX) inf_le_right hXL
    exact (le_inf_sup_of_le_normalizer hSL hSX hX).trans
      (sup_le_sup_right (le_inf inf_le_right hle) S)
  have hBle : B ⊔ S ≤ L ⊔ S := sup_le_sup_right inf_le_left S
  have hBSL : (B ⊔ S) ⊓ L ≤ B := by
    rintro y ⟨hy, hyL⟩
    have hy' : y ∈ ((B : Set G) * (S : Set G)) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left B S hSB]
      exact hy
    obtain ⟨b, hb, s, hs, rfl⟩ := hy'
    have hsL : s ∈ L := by
      have := L.mul_mem (L.inv_mem hb.1) hyL
      simpa using this
    exact B.mul_mem hb ⟨hsL, Subgroup.le_normalizer ⟨hs, hsL⟩⟩
  have hne : B ⊔ S ≠ L ⊔ S := by
    intro heq
    apply hR.borel_ne
    refine le_antisymm inf_le_left fun l hl => ?_
    have : l ∈ (B ⊔ S) ⊓ L := ⟨heq ▸ Subgroup.mem_sup_left hl, hl⟩
    exact hBSL this
  refine Set.ext fun N => ⟨fun hN => ?_, fun hN => ?_⟩
  · obtain ⟨hNmax, hSN⟩ := hN
    rw [Set.mem_singleton_iff]
    have h1 : N ≤ B ⊔ S := hkey N hSN hNmax.1.le hNmax.1.ne
    by_contra hne'
    exact hne (hNmax.2 (B ⊔ S) (lt_of_le_of_ne h1 hne') hBle)
  · rw [Set.mem_singleton_iff] at hN
    subst hN
    refine ⟨⟨lt_of_le_of_ne hBle hne, fun K hK hKle => ?_⟩, le_sup_right⟩
    by_contra hKne
    exact (lt_irrefl _) (lt_of_lt_of_le hK (hkey K (le_sup_right.trans hK.le) hKle hKne))

omit [Finite G] in
theorem oTwoUpper_eq_bot_of_isPGroup {P : Subgroup G} (hP : IsPGroup 2 P) : oTwoUpper P = ⊥ := by
  refine le_bot_iff.mp ((Subgroup.closure_le (⊥ : Subgroup G)).mpr fun x hx => ?_)
  obtain ⟨k, hk⟩ := hP ⟨x, hx.1⟩
  have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hdvd : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hodd := hx.2
  rw [hj] at hodd
  have hj0 : j = 0 := by
    by_contra hne
    exact Nat.not_even_iff_odd.mpr hodd (Nat.even_pow.mpr ⟨even_two, hne⟩)
  rw [hj0, pow_zero, orderOf_eq_one_iff] at hj
  exact (Subgroup.mem_bot).mpr hj

section Hyp501

variable {T M L : Subgroup G} {n : ℕ} (h : Hyp5_0_1 G T M L n)
include h

theorem hyp501_charTwo : CharTwo L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (quasithinGenFitting_eq_pCoreOf_iff L 2).mp h.faithful.2.2.1

theorem hyp501_L_ne_bot : L ≠ ⊥ := h.maximal.1.2.1.1

theorem hyp501_pCoreOf_ne_bot : pCoreOf 2 L ≠ ⊥ :=
  pCoreOf_ne_bot_of_charTwo (hyp501_charTwo h) (hyp501_L_ne_bot h)

theorem hyp501_eq_oTwoUpper : L = oTwoUpper L := eq_oTwoUpper_of_perfect h.commutator_eq

theorem hyp501_center_eq_bot : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ := by
  have hsimp := h.isSimple
  rcases hsimp.eq_bot_or_eq_top_of_normal (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) with hb | ht
  · exact hb
  · exfalso
    obtain ⟨-, -, a, b, hab⟩ := h.isQuasisimple
    have h1 : ∀ x : (↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L),
        x = 1 := by
      intro x
      obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective x
      exact (QuotientGroup.eq_one_iff q).mpr (ht ▸ Subgroup.mem_top q)
    exact hab (by rw [h1 a, h1 b])

theorem hyp501_eq_of_subnormal {K : Subgroup G} (hKL : K ≤ L) (hK : IsSubnormal K L)
    (hK2 : K = oTwoUpper K) (hK1 : K ≠ ⊥) : K = L := by
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hπ
  have hsub : (K.subgroupOf L).IsSubnormal := (isSubnormal_iff_subgroupOf hKL).mp hK
  have hsubb : ((K.subgroupOf L).map π).IsSubnormal := by
    have := A3.subnormal_top_map (f := π) (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L))
      (A3.subnormal_top_iff.mpr hsub)
    exact A3.subnormal_top_iff.mp this
  rcases A3.eq_top_or_le_center_of_subnormal h.isQuasisimple hsubb with htop | hcen
  ·
    have hKP : K ⊔ pCoreOf 2 L = L := by
      refine le_antisymm (_root_.sup_le hKL (pCoreOf_le 2 L)) fun x hx => ?_
      have hmem : π ⟨x, hx⟩ ∈ (K.subgroupOf L).map π := by
        rw [htop]
        exact Subgroup.mem_top _
      obtain ⟨c, hc, hcx⟩ := hmem
      have ho' : π (c⁻¹ * ⟨x, hx⟩) = 1 := by rw [map_mul, map_inv, hcx, inv_mul_cancel]
      have ho : c⁻¹ * ⟨x, hx⟩ ∈ CFSG.pCore 2 ↥L := by
        rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at ho'
      have hker' : ((c⁻¹ * ⟨x, hx⟩ : ↥L) : G) ∈ pCoreOf 2 L := by
        refine ⟨c⁻¹ * ⟨x, hx⟩, ?_, rfl⟩
        exact ho
      have e : x = (c : G) * ((c⁻¹ * ⟨x, hx⟩ : ↥L) : G) := by simp
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hc))
        (Subgroup.mem_sup_right hker')
    have hKn : K ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
      hKL.trans (le_normalizer_pCoreOf 2 L)
    have hcomm : ((pCoreOf 2 L : Subgroup G) : Set G) * (K : Set G) =
        (K : Set G) * (pCoreOf 2 L : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ K hKn,
        ← Subgroup.coe_mul_of_left_le_normalizer_right K _ hKn, sup_comm]
    have h22 := (a4_2_2 hK2 hK (pCoreOf_le 2 L) (pCoreOf_isPGroup 2 L) hcomm).1
    rw [hKP, ← (hyp501_eq_oTwoUpper h)] at h22
    exact h22
  ·
    exfalso
    rw [(hyp501_center_eq_bot h)] at hcen
    have hKO : K ≤ pCoreOf 2 L := by
      intro k hk
      have hmem : π ⟨k, hKL hk⟩ ∈ (K.subgroupOf L).map π := ⟨⟨k, hKL hk⟩, hk, rfl⟩
      have h1 : π ⟨k, hKL hk⟩ = 1 := Subgroup.mem_bot.mp (hcen hmem)
      have h2 : (⟨k, hKL hk⟩ : ↥L) ∈ CFSG.pCore 2 ↥L := by
        rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      refine ⟨⟨k, hKL hk⟩, ?_, rfl⟩
      exact h2
    apply hK1
    rw [hK2]
    exact oTwoUpper_eq_bot_of_isPGroup ((pCoreOf_isPGroup 2 L).to_le hKO)

theorem hyp501_block_eq {S K : Subgroup G} (hK : IsBlock2 (L ⊔ S) K) (hKL : K ≤ L) :
    K = L := by
  have hKsub : IsSubnormal K (L ⊔ S) := (isSubnormal_iff_subgroupOf hK.2.1).mpr hK.2.2
  have hKsubL : IsSubnormal K L := A3.subnormal_of_le_of_le hKsub hKL le_sup_left
  have hK2 : K = oTwoUpper K := by
    refine le_antisymm ?_ (oTwoUpper_le K)
    have : ((oTwoUpper K).subgroupOf K).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer (le_normalizer_oTwoUpper K)
    have hN := hK.1.1 ((oTwoUpper K).subgroupOf K) ?_
    · intro k hk
      have : (⟨k, hk⟩ : ↥K) ∈ (oTwoUpper K).subgroupOf K := hN ▸ Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp this
    · intro x
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
      obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper K y.2
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact Subgroup.mem_subgroupOf.mpr (by simpa using hk)
  have hK1 : K ≠ ⊥ := by
    intro hbot
    have hlt := hK.1.2.2.2.2.1
    have hU : blockU K = ⊥ := by
      rw [blockU, hbot]
      exact Subgroup.commutator_bot_right _
    rw [hU] at hlt
    exact (not_lt_bot hlt)
  exact (hyp501_eq_of_subnormal h) hKL hKsubL hK2 hK1

end Hyp501

@[expose] def Cond431 (M L S TH : Subgroup G) : Prop :=
  IsPGroup 2 S ∧ S ≤ M ∧ IsSylowTwoOf TH (M ⊓ Subgroup.normalizer (S : Set G)) ∧
    IsSylowTwoOf (S ⊓ L) L ∧ IsUniqueM (L ⊔ TH) M

theorem cond431_map_conj {M L S TH : Subgroup G} (hLM : M ≤ Subgroup.normalizer (L : Set G))
    (hc : Cond431 M L S TH) {m : G} (hm : m ∈ M) :
    Cond431 M L (S.map (MulAut.conj m).toMonoidHom) (TH.map (MulAut.conj m).toMonoidHom) := by
  obtain ⟨hS2, hSM, hTH, hSL, hU⟩ := hc
  have hmM : m ∈ Subgroup.normalizer (M : Set G) := Subgroup.le_normalizer hm
  have hmL : (L.map (MulAut.conj m).toMonoidHom) = L := map_conj_eq_of_mem_normalizer (hLM hm)
  refine ⟨hS2.map _, (map_conj_mono hSM m).trans (map_conj_le_of_mem_normalizer hmM), ?_, ?_, ?_⟩
  · rw [← map_conj_inf_normalizer hm]
    exact isSylowTwoOf_map_conj' hTH m
  · have := isSylowTwoOf_map_conj' hSL m
    rwa [Subgroup.map_inf_eq _ _ _ (MulAut.conj m).injective, hmL] at this
  · have := isUniqueM_map_conj hU hm
    rwa [Subgroup.map_sup, hmL] at this

omit [Finite G] in
theorem normalizer_map_conj_le_iff {M S : Subgroup G} {m : G} (hm : m ∈ M) :
    Subgroup.normalizer ((S.map (MulAut.conj m).toMonoidHom : Subgroup G) : Set G) ≤ M ↔
      Subgroup.normalizer (S : Set G) ≤ M := by
  have hmM : m ∈ Subgroup.normalizer (M : Set G) := Subgroup.le_normalizer hm
  rw [← Subgroup.map_equiv_normalizer_eq]
  constructor
  · intro h
    have h1 := map_conj_mono h m⁻¹
    rwa [map_conj_inv_map_conj, map_conj_eq_of_mem_normalizer (inv_mem hmM)] at h1
  · intro h
    exact (map_conj_mono h m).trans (map_conj_le_of_mem_normalizer hmM)

theorem lemma_4_3_1 (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six) {T M L : Subgroup G}
    {n : ℕ} (h : Hyp5_0_1 G T M L n) {S TH : Subgroup G} (hS2 : IsPGroup 2 S) (hSM : S ≤ M)
    (hTH : IsSylowTwoOf TH (M ⊓ Subgroup.normalizer (S : Set G)))
    (hSL : IsSylowTwoOf (S ⊓ L) L) (hU : IsUniqueM (L ⊔ TH) M) :
    Subgroup.normalizer (S : Set G) ≤ M := by
  classical
  by_contra hcon
  set 𝒞 : Set (Subgroup G × Subgroup G) :=
    {p | Cond431 M L p.1 p.2 ∧ ¬ Subgroup.normalizer (p.1 : Set G) ≤ M} with h𝒞
  obtain ⟨⟨S₀, T₀⟩, h₀, hmax₀⟩ := Set.exists_max_image 𝒞 (fun p => Nat.card p.2)
    (Set.toFinite _) ⟨(S, TH), ⟨hS2, hSM, hTH, hSL, hU⟩, hcon⟩
  have hTM : IsSylowTwoOf T M := h.isSylowTwoOf h.T_le
  obtain ⟨P, hP, hT₀P⟩ := exists_isSylowTwoOf_ge (h₀.1.2.2.1.1.trans inf_le_left)
    h₀.1.2.2.1.2.1
  obtain ⟨c, hc, hcP⟩ := exists_conj_of_isSylowTwoOf hTM hP
  have hm : c⁻¹ ∈ M := M.inv_mem hc
  set S₁ := S₀.map (MulAut.conj c⁻¹).toMonoidHom with hS₁
  set T₁ := T₀.map (MulAut.conj c⁻¹).toMonoidHom with hT₁
  have hc₁ : Cond431 M L S₁ T₁ := cond431_map_conj h.normal h₀.1 hm
  have hn₁ : ¬ Subgroup.normalizer (S₁ : Set G) ≤ M := fun hle =>
    h₀.2 ((normalizer_map_conj_le_iff hm).mp hle)
  have hcard₁ : Nat.card T₁ = Nat.card T₀ :=
    Nat.card_congr (T₀.equivMapOfInjective _ (MulAut.conj c⁻¹).injective).toEquiv.symm
  have hmax₁ : ∀ p ∈ 𝒞, Nat.card p.2 ≤ Nat.card T₁ := fun p hp => hcard₁ ▸ hmax₀ p hp
  have hT₁T : T₁ ≤ T := by
    intro x hx
    rw [hT₁, mem_map_conj_iff, inv_inv] at hx
    have := (hcP _).mp (hT₀P hx)
    simpa [mul_assoc] using this
  obtain ⟨hS₁2, hS₁M, hT₁s, hS₁L, hU₁⟩ := hc₁
  have hS₁T₁ : S₁ ≤ T₁ :=
    le_of_normal_of_isSylowTwoOf hT₁s (le_inf hS₁M Subgroup.le_normalizer)
      (Subgroup.normal_subgroupOf_of_le_normalizer inf_le_right) hS₁2
  have hT₁2 : IsPGroup 2 T₁ := hT₁s.2.1
  have hT₁N : T₁ ≤ Subgroup.normalizer (S₁ : Set G) := hT₁s.1.trans inf_le_right
  have hT₁M : T₁ ≤ M := hT₁s.1.trans inf_le_left
  have hT₁L : T₁ ≤ Subgroup.normalizer (L : Set G) := hT₁M.trans h.normal
  have hTL : IsSylowTwoOf (T ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal (h.isSylowTwoOf le_sup_right) le_sup_left h.sup_le_normalizer
  have hS₁T₁L : S₁ ⊓ L ≤ T₁ ⊓ L := inf_le_inf_right L hS₁T₁
  have hT₁Leq : T₁ ⊓ L = T ⊓ L := by
    have h1 := (isSylowTwoOf_iff_maximal.mp hS₁L).2.2 (T ⊓ L) inf_le_right
      (h.sylow.1.to_le inf_le_left) (hS₁T₁L.trans (inf_le_inf_right L hT₁T))
    exact le_antisymm (inf_le_inf_right L hT₁T) (h1.trans hS₁T₁L)
  have hT₁Lsyl : IsSylowTwoOf (T₁ ⊓ L) L := hT₁Leq ▸ hTL
  have hT₁syl : IsSylowTwoOf T₁ (Subgroup.normalizer (S₁ : Set G)) := by
    by_cases hT₁eq : T₁ = T
    · rw [hT₁eq]
      exact isSylowTwoOf_of_le h.sylow (hT₁eq ▸ hT₁N)
    have hlt : T₁ < T := lt_of_le_of_ne hT₁T hT₁eq
    have hNT₁ : Subgroup.normalizer (T₁ : Set G) ≤ M := by
      by_contra hn
      have hX : T ⊓ Subgroup.normalizer (T₁ : Set G) ≤ M ⊓ Subgroup.normalizer (T₁ : Set G) :=
        inf_le_inf_right _ h.T_le
      obtain ⟨T₂, hT₂, hXT₂⟩ := exists_isSylowTwoOf_ge hX (h.sylow.1.to_le inf_le_left)
      have hT₁T₂ : T₁ < T₂ := by
        obtain ⟨y, hyT, hyN, hyT₁⟩ := exists_mem_normalizer_not_mem h.sylow.1 hlt
        refine lt_of_le_of_ne ((le_inf hT₁T Subgroup.le_normalizer).trans hXT₂) fun e => ?_
        exact hyT₁ (e ▸ hXT₂ ⟨hyT, hyN⟩)
      have hc₂ : Cond431 M L T₁ T₂ := by
        refine ⟨hT₁2, hT₁M, hT₂, hT₁Lsyl, isUniqueM_mono hU₁ (sup_le_sup_left hT₁T₂.le L) ?_⟩
        exact _root_.sup_le h.L_le (hT₂.1.trans inf_le_left)
      have := hmax₁ (T₁, T₂) ⟨hc₂, hn⟩
      exact absurd this (not_le.mpr (Subgroup.card_lt_of_lt hT₁T₂))
    refine isSylowTwoOf_iff_maximal.mpr ⟨hT₁N, hT₁2, fun Q hQ hQ2 hT₁Q => ?_⟩
    by_contra hQT₁
    obtain ⟨y, hyQ, hyN, hyT₁⟩ := exists_mem_normalizer_not_mem hQ2
      (lt_of_le_of_ne hT₁Q fun e => hQT₁ (e ▸ le_rfl))
    have hyM : y ∈ M := hNT₁ hyN
    have hsub : T₁ ⊔ Subgroup.zpowers y ≤ M ⊓ Subgroup.normalizer (S₁ : Set G) :=
      _root_.sup_le hT₁s.1 (Subgroup.zpowers_le.mpr ⟨hyM, hQ hyQ⟩)
    have h2 : IsPGroup 2 ↥(T₁ ⊔ Subgroup.zpowers y) :=
      hQ2.to_le (_root_.sup_le hT₁Q (Subgroup.zpowers_le.mpr hyQ))
    have hle := (isSylowTwoOf_iff_maximal.mp hT₁s).2.2 _ hsub h2 le_sup_left
    exact hyT₁ (hle (Subgroup.mem_sup_right (Subgroup.mem_zpowers y)))
  have hO2 : pCoreOf 2 (L ⊔ T₁) ≠ ⊥ := by
    intro h0
    apply (hyp501_pCoreOf_ne_bot h)
    refine le_bot_iff.mp (h0 ▸ le_pCoreOf_of_le_normalizer 2
      ((pCoreOf_le 2 L).trans le_sup_left) ?_ (pCoreOf_isPGroup 2 L))
    exact (_root_.sup_le Subgroup.le_normalizer hT₁L).trans (normalizer_le_normalizer_pCoreOf 2 L)
  have hS₁1 : S₁ ≠ ⊥ := by
    intro h0
    apply (hyp501_pCoreOf_ne_bot h)
    have := pCoreOf_two_le_of_isSylowTwoOf hS₁L
    rw [h0, bot_inf_eq] at this
    exact le_bot_iff.mp this
  have hO2U : oTwoUpper (L ⊔ T₁) = L :=
    oTwoUpper_sup_eq_of_normal (hyp501_eq_oTwoUpper h) hT₁2 hT₁L
  have hHyp : HypC51 (L ⊔ T₁) (Subgroup.normalizer (S₁ : Set G)) S₁ T₁ := by
    refine ⟨isSQTKSub_of_inH h.qtke h.simple h.nonabelian (T := L ⊔ T₁) ⟨le_rfl, hO2⟩,
      isSQTKSub_of_inH h.qtke h.simple h.nonabelian (T := Subgroup.normalizer (S₁ : Set G))
        ⟨le_rfl, ?_⟩,
      Vol2Native.L239.charTwo_sup_of_le_normalizer (hyp501_charTwo h) hT₁2 hT₁L,
      isSylowTwoOf_sup_of_inf hT₁2 hT₁L hT₁Lsyl,
      ⟨_, isUniqueMaxOver_sup hT₁L (by rw [hT₁Leq]; exact h.rankOneAt hR)⟩,
      hS₁T₁, hT₁N, ?_, le_rfl⟩
    · intro h0
      apply hS₁1
      exact le_bot_iff.mp (h0 ▸ le_pCoreOf_normalizer 2 S₁ hS₁2)
    · rw [hO2U]
      exact isSylowTwoOf_sup_of_inf hS₁2 (hS₁M.trans h.normal) hS₁L
  by_cases hNC : ∃ X : Subgroup G, X ≤ S₁ ∧ X ≠ ⊥ ∧
      L ⊔ T₁ ≤ Subgroup.normalizer (X : Set G) ∧
      Subgroup.normalizer (S₁ : Set G) ≤ Subgroup.normalizer (X : Set G)
  ·
    obtain ⟨X, hXS, hX1, hHX, hMX⟩ := hNC
    exact hn₁ (hMX.trans (isUniqueM_normalizer_le hU₁ hX1 (hS₁2.to_le hXS) hHX))
  ·
    have hNC' : C5.NoCommonNormal S₁ (L ⊔ T₁) (Subgroup.normalizer (S₁ : Set G)) :=
      fun X hXS hX1 hHX hMX => hNC ⟨X, hXS, hX1, hHX, hMX⟩
    obtain ⟨K₁, K₂, hne, hK₁, hK₂, -, -, hKs⟩ := hC G (L ⊔ T₁) _ S₁ T₁ hHyp hS₁1 hNC' hT₁syl
    rw [hO2U] at hKs
    have h1 := (hyp501_block_eq h) hK₁ (hKs ▸ le_sup_left)
    have h2 := (hyp501_block_eq h) hK₂ (hKs ▸ le_sup_right)
    exact hne (h1.trans h2.symm)

end CFSG.Quasithin.H13.Ch4
