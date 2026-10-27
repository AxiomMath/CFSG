module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeLem125
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeFive
public import CFSG.Quasithin.H13.VolIC113
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238FourSylow
public import CFSG.Quasithin.EmptyFaithful.S1469CaseA0
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Native
public import CFSG.Quasithin.Vol2.Ch1Nine
public import CFSG.GroupTheory.SubnormalJoin
public import CFSG.Quasithin.Background.C2Basic

public section

namespace CFSG.Quasithin.H13.CTK

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem le_of_perfect_of_le_sup {K T X : Subgroup G} (hT : IsPGroup 2 T)
    (hTN : T ≤ Subgroup.normalizer (K : Set G)) (hX : X ≤ K ⊔ T) (hXp : ⁅X, X⁆ = X) :
    X ≤ K := by
  set Y := K ⊔ T with hY
  have hKY : K ≤ Y := le_sup_left
  have hnorm : (K.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKY).mpr
      (sup_le Subgroup.le_normalizer hTN)
  let π : ↥Y →* ↥Y ⧸ K.subgroupOf Y := QuotientGroup.mk' _
  have hmul : ((Y : Set G)) = (K : Set G) * (T : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left K T hTN
  have hQ2 : IsPGroup 2 (↥Y ⧸ K.subgroupOf Y) := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ q
    have hy : (y : G) ∈ (K : Set G) * (T : Set G) := by
      rw [← hmul]; exact y.2
    obtain ⟨k, hk, t, ht, hkt⟩ := hy
    obtain ⟨n, hn⟩ := hT ⟨t, ht⟩
    refine ⟨n, ?_⟩
    have hyk : y = ⟨k, hKY hk⟩ * ⟨t, Subgroup.mem_sup_right ht⟩ := Subtype.ext hkt.symm
    have h1 : π ⟨k, hKY hk⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr hk
    have h2 : (⟨t, Subgroup.mem_sup_right ht⟩ : ↥Y) ^ 2 ^ n = 1 := by
      apply Subtype.ext
      have := congrArg Subtype.val hn
      simpa using this
    show π y ^ 2 ^ n = 1
    rw [hyk, map_mul, h1, one_mul, ← map_pow, h2, map_one]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsolv : Group.IsSolvable (↥Y ⧸ K.subgroupOf Y) := by
    have : Group.IsNilpotent (↥Y ⧸ K.subgroupOf Y) := hQ2.isNilpotent
    infer_instance
  set X' := X.subgroupOf Y with hX'
  have hX'p : ⁅X', X'⁆ = X' := by
    apply Subgroup.map_injective Y.subtype_injective
    rw [Subgroup.map_commutator, hX', Subgroup.map_subgroupOf_eq_of_le hX, hXp]
  set H := X'.map π with hH
  have hHp : ⁅H, H⁆ = H := by
    rw [hH, ← Subgroup.map_commutator, hX'p]
  have hHperf : Group.IsPerfect ↥H := (Subgroup.isPerfect_iff (H := H)).2 hHp
  have hHs : Group.IsSolvable ↥H := inferInstance
  have hHbot : H = ⊥ := by
    by_contra hne
    have : Nontrivial ↥H := (Subgroup.nontrivial_iff_ne_bot H).2 hne
    exact Group.IsPerfect.not_isSolvable ↥H hHs
  have hker : X' ≤ K.subgroupOf Y := by
    intro x hx
    have : π x ∈ H := Subgroup.mem_map_of_mem π hx
    rw [hHbot, Subgroup.mem_bot] at this
    exact (QuotientGroup.eq_one_iff _).mp this
  intro x hx
  have hxY : x ∈ Y := hX hx
  have h1 : (⟨x, hxY⟩ : ↥Y) ∈ X' := Subgroup.mem_subgroupOf.mpr hx
  exact Subgroup.mem_subgroupOf.mp (hker h1)


@[expose] def ExclA5BlockFor (P : ∀ (S : Type) [Group S], Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (J D K V T₁ T₂ : Subgroup G),
    CFSG.IsQuasisimple ↥J → P (↥J ⧸ Subgroup.center ↥J) →
    Nat.card ↥D = 2 → D ≤ Subgroup.centralizer (J : Set G) → pCoreOf 2 (J ⊔ D) = D →
    K ≤ J → IsShort2 K → IsAltType K 5 → pCoreOf 2 K = V → Nat.card ↥V = 16 →
    D ≤ T₁ → T₁ ≤ J ⊔ D → T₁ ≤ Subgroup.normalizer (K : Set G) →
    (J ⊔ D) ⊓ Subgroup.normalizer ((V ⊔ D : Subgroup G) : Set G) = K ⊔ T₁ →
    IsSylowTwoOf T₁ (K ⊔ T₁) →
    IsSylowTwoOf T₂ (J ⊔ D) → T₁ ≤ T₂ → T₁.relIndex T₂ ≤ 2 → False

@[expose] def ExclA5Block : Prop :=
  ExclA5BlockFor fun S _ => CFSG.Milestones.SQTKSimpleList S

theorem ExclA5BlockFor.mono {P Q : ∀ (S : Type) [Group S], Prop}
    (hPQ : ∀ (S : Type) [Group S], P S → Q S) (h : ExclA5BlockFor Q) : ExclA5BlockFor P :=
  fun G _ _ J D K V T₁ T₂ hJ hP => h G J D K V T₁ T₂ hJ (hPQ _ hP)

theorem ExclA5BlockFor.or {P Q : ∀ (S : Type) [Group S], Prop} (hP : ExclA5BlockFor P)
    (hQ : ExclA5BlockFor Q) : ExclA5BlockFor fun S _ => P S ∨ Q S :=
  fun G _ _ J D K V T₁ T₂ hJ hPQ => hPQ.elim (hP G J D K V T₁ T₂ hJ) (hQ G J D K V T₁ T₂ hJ)

@[expose] def SQTKAltFam (S : Type) [Group S] : Prop :=
  ∃ n : ℕ, 5 ≤ n ∧ n ≤ 8 ∧ Nonempty (S ≃* alternatingGroup (Fin n))

@[expose] def SQTKOddFam (S : Type) [Group S] : Prop :=
  ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
    ((∃ f : ℕ, (f = 1 ∨ f = 2) ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel S .PSL 2 p f) ∨
      CFSG.Assembly.LowTwoRank.StatedClassicalModel S .PSL 3 p 1 ∨
      CFSG.Assembly.LowTwoRank.StatedClassicalModel S .PSU 3 p 1)

@[expose] def SQTKTwoFam (S : Type) [Group S] : Prop :=
  ((∃ f : ℕ,
    (2 ≤ f ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel S .PSL 2 2 f) ∨
    (1 ≤ f ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel S .PSL 3 2 f) ∨
    (2 ≤ f ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel S .PSU 3 2 f) ∨
    (2 ≤ f ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel S .PSp 2 2 f) ∨
    (2 ≤ f ∧ CFSG.Blueprint.ChevalleyExceptionalModel S .G2 2 f) ∨
    (1 ≤ f ∧ CFSG.Blueprint.ChevalleyExceptionalModel S .trialityD4 2 f) ∨
    (Odd f ∧ 3 ≤ f ∧ CFSG.Blueprint.ReeTitsModel S .twistedF4 2 f) ∨
    (Odd f ∧ 3 ≤ f ∧ CFSG.Blueprint.SuzukiModel S 2 f)) ∨
    CFSG.Blueprint.ReeTitsModel S .Tits 2 1)

@[expose] def SQTKL45Fam (S : Type) [Group S] : Prop :=
  ∃ n : ℕ, (n = 4 ∨ n = 5) ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel S .PSL n 2 1

@[expose] def SQTKSporFam (S : Type) [Group S] : Prop :=
  ∃ s : TauCeti.SporadicName,
    (s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .M24 ∨
      s = .J1 ∨ s = .J2 ∨ s = .J4 ∨ s = .HS ∨ s = .He ∨ s = .Ru) ∧
    Nonempty (S ≃* CFSG.Blueprint.NativeSporadic.Carrier s)

theorem sqtkSimpleList_iff (S : Type) [Group S] :
    CFSG.Milestones.SQTKSimpleList S ↔
      SQTKAltFam S ∨ SQTKOddFam S ∨ SQTKTwoFam S ∨ SQTKL45Fam S ∨ SQTKSporFam S := Iff.rfl

theorem exclA5Block_of_families (h1 : ExclA5BlockFor fun S _ => SQTKAltFam S)
    (h2 : ExclA5BlockFor fun S _ => SQTKOddFam S) (h3 : ExclA5BlockFor fun S _ => SQTKTwoFam S)
    (h4 : ExclA5BlockFor fun S _ => SQTKL45Fam S)
    (h5 : ExclA5BlockFor fun S _ => SQTKSporFam S) : ExclA5Block :=
  ExclA5BlockFor.mono (fun S _ h => (sqtkSimpleList_iff S).1 h)
    (h1.or (h2.or (h3.or (h4.or h5))))

section Facts

variable {K V : Subgroup G}

theorem blockU_eq_of_alt5 (hKs : IsShort2 K) (hKa : IsAltType K 5) (hKV : pCoreOf 2 K = V)
    (hV16 : Nat.card ↥V = 16) : blockU K = V := by
  obtain ⟨P⟩ := AppC.nonempty_a5pi hKs hKa
  have hU : Nat.card ↥(blockU K) = 16 := P.card_blockU
  have hle : blockU K ≤ V := hKV ▸ (C1.blockU_le_blockQ hKs)
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hU, hV16])


theorem irreducible_of_alt5 (hKs : IsShort2 K) (hKa : IsAltType K 5) (hKV : pCoreOf 2 K = V)
    (hV16 : Nat.card ↥V = 16) {W : Subgroup G} (hWV : W ≤ V)
    (hWK : K ≤ Subgroup.normalizer (W : Set G)) : W = ⊥ ∨ W = V := by
  have hU := blockU_eq_of_alt5 hKs hKa hKV hV16
  have hZ : blockZ K = ⊥ := AppC.blockZ_eq_bot_of_alt5 hKs hKa
  have h5 := hKs.2.2.2.2.2 W (by rw [hZ]; exact bot_le) (hU ▸ hWV) hWK
  rw [hZ, hU] at h5
  exact h5

theorem isElemAbelian_V (hKs : IsShort2 K) (hKa : IsAltType K 5) (hKV : pCoreOf 2 K = V)
    (hV16 : Nat.card ↥V = 16) : IsElemAbelian 2 V := by
  have hU := blockU_eq_of_alt5 hKs hKa hKV hV16
  rw [← hU]
  exact AppC.isElemAbelian_blockU hKs

theorem relIndex_le_of_card_le {A B C : Subgroup G} (hAB : A ≤ B) (hAC : A ≤ C)
    (hcard : Nat.card ↥B ≤ Nat.card ↥C) : A.relIndex B ≤ A.relIndex C := by
  have h1 := Subgroup.card_mul_index (A.subgroupOf B)
  have h2 := Subgroup.card_mul_index (A.subgroupOf C)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAB).toEquiv] at h1
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAC).toEquiv] at h2
  have hpos : 0 < Nat.card ↥A := Nat.card_pos
  change Nat.card ↥A * A.relIndex B = Nat.card ↥B at h1
  change Nat.card ↥A * A.relIndex C = Nat.card ↥C at h2
  have : Nat.card ↥A * A.relIndex B ≤ Nat.card ↥A * A.relIndex C := by rw [h1, h2]; exact hcard
  exact Nat.le_of_mul_le_mul_left this hpos

omit [Finite G] in
theorem map_conj_eq_of_mem_normalizer {C : Subgroup G} {x : G}
    (hC : x ∈ Subgroup.normalizer (C : Set G)) : C.map (MulAut.conj x).toMonoidHom = C := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hC w).mp hw
  · intro hz
    refine ⟨x⁻¹ * z * x, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp hC (x⁻¹ * z * x)).mpr (by simpa [mul_assoc] using hz)
    · simp [mul_assoc]

omit [Finite G] in
theorem mem_normalizer_sup {A B : Subgroup G} {x : G}
    (hA : x ∈ Subgroup.normalizer (A : Set G)) (hB : x ∈ Subgroup.normalizer (B : Set G)) :
    x ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  have hmap : (A ⊔ B).map (MulAut.conj x).toMonoidHom = A ⊔ B := by
    rw [Subgroup.map_sup, map_conj_eq_of_mem_normalizer hA, map_conj_eq_of_mem_normalizer hB]
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [← hmap]
    exact ⟨y, hy, rfl⟩
  · intro hy
    rw [← hmap] at hy
    obtain ⟨w, hw, hwy⟩ := hy
    have : w = y := (MulAut.conj x).injective hwy
    rwa [this] at hw

omit [Finite G] in
theorem map_conj_mul (K : Subgroup G) (a b : G) :
    K.map (MulAut.conj (a * b)).toMonoidHom =
      (K.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext z
  simp [mul_assoc]

omit [Finite G] in
theorem map_conj_one (K : Subgroup G) : K.map (MulAut.conj (1 : G)).toMonoidHom = K := by
  ext z
  simp

omit [Finite G] in
theorem conj_eq_of_ncard_two {H K : Subgroup G} (hcard : (conjSubgroupsBy H K).ncard = 2)
    {y : G} (hy : y ∈ H) (hy3 : y ^ 3 = 1) :
    K.map (MulAut.conj y).toMonoidHom = K := by
  set f : Subgroup G → Subgroup G := fun L => L.map (MulAut.conj y).toMonoidHom with hf
  have hK : K ∈ conjSubgroupsBy H K := ⟨1, H.one_mem, (map_conj_one K).symm⟩
  have hmem : ∀ L ∈ conjSubgroupsBy H K, f L ∈ conjSubgroupsBy H K := by
    rintro L ⟨t, ht, rfl⟩
    exact ⟨y * t, H.mul_mem hy ht, (map_conj_mul K y t).symm⟩
  have hinj : Function.Injective f := Subgroup.map_injective (MulAut.conj y).injective
  obtain ⟨a, b, hab, hS⟩ := Set.ncard_eq_two.mp hcard
  have h3 : f (f (f K)) = K := by
    show ((K.map (MulAut.conj y).toMonoidHom).map (MulAut.conj y).toMonoidHom).map
      (MulAut.conj y).toMonoidHom = K
    rw [← map_conj_mul, ← map_conj_mul, ← pow_two, ← pow_succ y 2]
    rw [show y ^ (2 + 1) = 1 from hy3, map_conj_one]
  show f K = K
  by_contra hne
  have hK1S : f K ∈ conjSubgroupsBy H K := hmem K hK
  have hK2S : f (f K) ∈ conjSubgroupsBy H K := hmem _ hK1S
  have hK2ne : f (f K) ≠ f K := fun h => hne (hinj h)
  rw [hS] at hK hK1S hK2S
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hK hK1S hK2S
  have hK2K : f (f K) = K := by
    rcases hK with h0 | h0 <;> rcases hK1S with h1 | h1 <;> rcases hK2S with h2 | h2 <;>
      first
      | exact absurd (h1.trans h0.symm) hne
      | exact absurd (h2.trans h1.symm) hK2ne
      | exact h2.trans h0.symm
  have := congrArg f hK2K
  rw [h3] at this
  exact hne this.symm

end Facts

section Main

variable {T K V D T₀ : Subgroup G}

theorem ctk_false_of_excl
    (hLS : LocalSQTK G) (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h39 : Vol2Native.A39ForSQTKCat) (h36 : Vol2Native.A36CoreForSQTKCat)
    (hl2 : L2MultiplierFact)
    (hlist : ∀ (X : Type) [Group X] [Finite X], CFSG.SectionRank.IsSQTKCat X →
      ∀ (H : Subgroup X) (N : Subgroup ↥H) [N.Normal] [IsSimpleGroup (↥H ⧸ N)],
        (∃ a b : ↥H ⧸ N, a * b ≠ b * a) → CFSG.Milestones.SQTKSimpleList (↥H ⧸ N))
    (hExcl : ExclA5Block)
    (hT : IsSylowTwoOf T ⊤)
    (hKs : IsShort2 K) (hKa : IsAltType K 5) (hKV : pCoreOf 2 K = V) (hV16 : Nat.card ↥V = 16)
    (hD2 : Nat.card ↥D = 2) (hDK : D ≤ Subgroup.centralizer (K : Set G))
    (hTQ : T ≤ Subgroup.normalizer ((V ⊔ D : Subgroup G) : Set G))
    (hT0T : T₀ ≤ T) (hT0D : T₀ ≤ Subgroup.centralizer (D : Set G))
    (hT0K : T₀ ≤ Subgroup.normalizer (K : Set G)) (hTKT0 : T ⊓ K ≤ T₀) (hDT0 : D ≤ T₀)
    (hT0i : T₀.relIndex T ≤ 2)
    (hTK : IsSylowTwoOf (T ⊓ K) K) (hCTK : T ⊓ Subgroup.centralizer (K : Set G) = D)
    (hAd : Subgroup.normalizer ((V ⊔ D : Subgroup G) : Set G) ⊓
      Subgroup.centralizer (D : Set G) ≤ K ⊔ T₀)
    (hy : ∃ y : G, y ∈ Subgroup.centralizer (D : Set G) ∧ orderOf y = 3 ∧
      y ∉ Subgroup.normalizer (V : Set G)) : False := by
  have hF2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set GD := Subgroup.centralizer (D : Set G) with hGD
  have hDcyc : IsCyclic ↥D := isCyclic_of_prime_card (p := 2) hD2
  have hDcomm : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := by
    intro a ha b hb
    have := (hDcyc.commGroup.mul_comm (⟨a, ha⟩ : ↥D) ⟨b, hb⟩)
    exact congrArg Subtype.val this
  have hDGD : D ≤ GD := fun a ha =>
    Subgroup.mem_centralizer_iff.2 fun b hb => (hDcomm b hb a ha)
  have hKGD : K ≤ GD := fun k hk =>
    Subgroup.mem_centralizer_iff.2 fun d hd => (Subgroup.mem_centralizer_iff.1 (hDK hd) k hk).symm
  have hDp : IsPGroup 2 D := IsPGroup.of_card (n := 1) (by rw [hD2]; norm_num)
  have hDne : D ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hD2
    omega
  have hDO : D ≤ pCoreOf 2 GD :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hDGD
      (Subgroup.centralizer_le_normalizer (D : Set G)) hDp
  have hOGD : pCoreOf 2 GD ≠ ⊥ := fun h => hDne (le_bot_iff.mp (h ▸ hDO))
  have hT0le : T₀ ≤ GD := hT0D
  have hTp : IsPGroup 2 T := hT.2.1
  have hT0p : IsPGroup 2 T₀ := hTp.to_le hT0T
  obtain ⟨TD, hT0TD, hTD⟩ := exists_isSylowTwoOf_of_le hT0le hT0p
  have hidx : T₀.relIndex TD ≤ 2 := by
    have hc : Nat.card ↥TD ≤ Nat.card ↥T := by
      have h1 := card_le_twoPart (U := TD) (H := ⊤) le_top hTD.isPGroup
      rw [hT.card_eq]
      exact h1
    exact (relIndex_le_of_card_le hT0TD hT0T hc).trans hT0i
  have hT0inf : T₀ ⊓ K = T ⊓ K := by
    ext x
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hx, hxK⟩
      exact ⟨hT0T hx, hxK⟩
    · rintro ⟨hxT, hxK⟩
      exact ⟨hTKT0 ⟨hxT, hxK⟩, hxK⟩
  have hsylT0 : IsSylowTwoOf T₀ (K ⊔ T₀) :=
    CFSG.Quasithin.isSylowTwoOf_sup_of_inf hT0p hT0K (hT0inf ▸ hTK)
  have hnormK : (K.subgroupOf (K ⊔ T₀)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hT0K)
  have hblk : IsBlock2 (K ⊔ T₀) K := ⟨hKs, le_sup_left, hnormK.isSubnormal⟩
  have hKcomp : K ∈ cComp (K ⊔ T₀) :=
    L238.mem_cComp_of_isChi0Block_nonsolvable hblk (Or.inr hKa)
  have hVne : V ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hV16
    omega
  have hV2 : IsPGroup 2 V := IsPGroup.of_card (n := 4) (by rw [hV16]; norm_num)
  have hVK : V ≤ K := hKV ▸ CFSG.LieType.BorelTits.pCoreOf_le 2 K
  have hVT0 : K ⊔ T₀ ≤ Subgroup.normalizer (V : Set G) := by
    refine sup_le ?_ (hT0K.trans ?_)
    · rw [← hKV]; exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K
    · rw [← hKV]; exact CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K
  have hOKT0 : pCoreOf 2 (K ⊔ T₀) ≠ ⊥ := by
    intro h
    apply hVne
    rw [eq_bot_iff, ← h]
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hVK.trans le_sup_left) hVT0 hV2
  have hloc : quasithinIsLocal T₀ K := ⟨hT0p, hKcomp, hsylT0.2.2, hOKT0⟩
  obtain ⟨KD, ⟨hKDc, hKKD⟩, -⟩ :=
    Vol2Native.lemma_1_2_5 hLS h37 h39 hOGD hTD hT0TD hidx hloc hKGD
  have hKDGD : KD ≤ GD := le_of_mem_cComp hKDc
  have hKDperf : ⁅KD, KD⁆ = KD := perfect_of_mem_cComp hKDc
  have hVGD : V ≤ GD := hVK.trans hKGD
  have hDKD : D ≤ Subgroup.centralizer (KD : Set G) := fun d hd =>
    Subgroup.mem_centralizer_iff.2 fun k hk =>
      (Subgroup.mem_centralizer_iff.1 (hKDGD hk) d hd).symm
  set Y := KD ⊔ D with hY
  have hYGD : Y ≤ GD := sup_le hKDGD hDGD
  have hKY : K ≤ Y := hKKD.trans le_sup_left
  have hDY : D ≤ Y := le_sup_right
  have hU : blockU K = V := blockU_eq_of_alt5 hKs hKa hKV hV16
  have hT0C : T₀ ⊓ Subgroup.centralizer (K : Set G) = D := by
    apply le_antisymm
    · intro x hx
      rw [← hCTK]
      exact Subgroup.mem_inf.2 ⟨hT0T hx.1, hx.2⟩
    · intro x hx
      exact Subgroup.mem_inf.2 ⟨hDT0 hx, hDK hx⟩
  set T₁ := T₀ ⊓ Y with hT1
  have hT1T0 : T₁ ≤ T₀ := inf_le_left
  have hT1N : T₁ ≤ Subgroup.normalizer (K : Set G) := hT1T0.trans hT0K
  have hT1p : IsPGroup 2 T₁ := hT0p.to_le hT1T0
  have hDT1 : D ≤ T₁ := le_inf hDT0 hDY
  have hT1inf : T₁ ⊓ K = T ⊓ K := by
    rw [← hT0inf]
    ext x
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨⟨hx0, _⟩, hxK⟩
      exact ⟨hx0, hxK⟩
    · rintro ⟨hx0, hxK⟩
      exact ⟨⟨hx0, hKY hxK⟩, hxK⟩
  have hsylT1 : IsSylowTwoOf T₁ (K ⊔ T₁) :=
    CFSG.Quasithin.isSylowTwoOf_sup_of_inf hT1p hT1N (hT1inf ▸ hTK)
  have hO2T1 : pCoreOf 2 (K ⊔ T₁) = V ⊔ D := by
    have h := (CFSG.Quasithin.H13.VolI.stmtC113c G K T₁ hsylT1 hT1N hKs hKa).1
    rw [hU] at h
    rw [h]
    have hC : T₁ ⊓ Subgroup.centralizer (K : Set G) = D := by
      apply le_antisymm
      · intro x hx
        rw [← hT0C]
        exact Subgroup.mem_inf.2 ⟨hT1T0 hx.1, hx.2⟩
      · intro x hx
        exact Subgroup.mem_inf.2 ⟨hDT1 hx, hDK hx⟩
    rw [hC]
  have hKN : K ≤ Subgroup.normalizer ((V ⊔ D : Subgroup G) : Set G) := by
    intro x hx
    refine mem_normalizer_sup ?_ ?_
    · rw [← hKV]
      exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K hx
    · exact Subgroup.centralizer_le_normalizer (D : Set G) (hKGD hx)
  have hT1Q : T₁ ≤ Subgroup.normalizer ((V ⊔ D : Subgroup G) : Set G) :=
    (hT1T0.trans hT0T).trans hTQ
  have hYN : Y ⊓ Subgroup.normalizer ((V ⊔ D : Subgroup G) : Set G) = K ⊔ T₁ := by
    apply le_antisymm
    · intro x hx
      have hxGD : x ∈ GD := hYGD hx.1
      have hx' : x ∈ K ⊔ T₀ := hAd (Subgroup.mem_inf.2 ⟨hx.2, hxGD⟩)
      have hmul : ((K ⊔ T₀ : Subgroup G) : Set G) = (K : Set G) * (T₀ : Set G) :=
        Subgroup.coe_mul_of_right_le_normalizer_left K T₀ hT0K
      have hx'' : x ∈ (K : Set G) * (T₀ : Set G) := by
        rw [← hmul]
        exact hx'
      obtain ⟨k, hk, t, ht, rfl⟩ := hx''
      have htY : t ∈ Y := by
        have : t = k⁻¹ * (k * t) := by group
        rw [this]
        exact Y.mul_mem (Y.inv_mem (hKY hk)) hx.1
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hk) (Subgroup.mem_sup_right ⟨ht, htY⟩)
    · exact le_inf (sup_le hKY inf_le_right) (sup_le hKN hT1Q)
  have hQY : V ⊔ D ≤ Y := sup_le (hVK.trans hKY) hDY
  have hpc : pCoreOf 2 Y ≤ V ⊔ D := by
    refine pCoreOf_le_of_eq_pCoreOf_normalizer hQY ?_
    rw [hYN, hO2T1]
  have hYnD : Y ≤ Subgroup.normalizer (D : Set G) :=
    hYGD.trans (Subgroup.centralizer_le_normalizer (D : Set G))
  have hDR : D ≤ pCoreOf 2 Y :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hDY hYnD hDp
  have hRY : Y ≤ Subgroup.normalizer ((pCoreOf 2 Y : Subgroup G) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y
  obtain ⟨y, hyGD, hy3, hyV⟩ := hy
  have hyKD : y ∈ Subgroup.normalizer (KD : Set G) := by
    rcases Vol2Native.lemma_1_2_1_three hLS h37 h38 hOGD hKDc with hn | ⟨hcard, -⟩
    · exact (Subgroup.normal_subgroupOf_iff_le_normalizer hKDGD).mp hn hyGD
    · have hy3' : y ^ 3 = 1 := by
        have := pow_orderOf_eq_one y
        rwa [hy3] at this
      have hmap := conj_eq_of_ncard_two hcard hyGD hy3'
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        have : y * h * y⁻¹ ∈ KD.map (MulAut.conj y).toMonoidHom := ⟨h, hh, by simp⟩
        rwa [hmap] at this
      · intro hh
        rw [← hmap] at hh
        obtain ⟨w, hw, hwh⟩ := hh
        have : w = h := (MulAut.conj y).injective (by simpa using hwh)
        rwa [this] at hw
  have hKnR : K ≤ Subgroup.normalizer ((pCoreOf 2 Y ⊓ V : Subgroup G) : Set G) := by
    intro x hx
    refine Subgroup.inf_normalizer_le_normalizer_inf ⟨hRY (hKY hx), ?_⟩
    rw [← hKV]
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K hx
  have hRD : pCoreOf 2 Y = D := by
    rcases irreducible_of_alt5 hKs hKa hKV hV16 (inf_le_right : pCoreOf 2 Y ⊓ V ≤ V) hKnR
      with hbot | hV
    ·
      apply le_antisymm _ hDR
      intro r hr
      have hrQ : r ∈ V ⊔ D := hpc hr
      have hmulQ : ((V ⊔ D : Subgroup G) : Set G) = (V : Set G) * (D : Set G) :=
        Subgroup.coe_mul_of_left_le_normalizer_right V D
          (fun v hv => Subgroup.centralizer_le_normalizer (D : Set G) (hVGD hv))
      have hrQ' : r ∈ (V : Set G) * (D : Set G) := by
        rw [← hmulQ]
        exact hrQ
      obtain ⟨v, hv, d, hd, rfl⟩ := hrQ'
      have hvR : v ∈ pCoreOf 2 Y := by
        have : v = (v * d) * d⁻¹ := by group
        rw [this]
        exact Subgroup.mul_mem _ hr (Subgroup.inv_mem _ (hDR hd))
      have : v ∈ pCoreOf 2 Y ⊓ V := ⟨hvR, hv⟩
      rw [hbot, Subgroup.mem_bot] at this
      subst this
      simpa using hd
    ·
      exfalso
      have hVR : V ≤ pCoreOf 2 Y := by
        rw [← hV]
        exact inf_le_left
      have hRQ : pCoreOf 2 Y = V ⊔ D := le_antisymm hpc (sup_le hVR hDR)
      have hYle : Y ≤ K ⊔ T₁ := by
        intro x hx
        rw [← hYN]
        refine Subgroup.mem_inf.2 ⟨hx, ?_⟩
        have := hRY hx
        rwa [hRQ] at this
      have hKDK : KD ≤ K :=
        le_of_perfect_of_le_sup hT1p hT1N (le_sup_left.trans hYle) hKDperf
      have hKDeq : KD = K := le_antisymm hKDK hKKD
      apply hyV
      rw [hKDeq] at hyKD
      rw [← hKV]
      exact CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K hyKD
  have hDCKD' : D ≤ Subgroup.centralizer ((pCoreOf 2 KD : Subgroup G) : Set G) :=
    hDKD.trans (Subgroup.centralizer_le (CFSG.LieType.BorelTits.pCoreOf_le 2 KD))
  have hcenter : pCoreOf 2 KD ≤ centerOf KD := by
    intro x hx
    have hle : pCoreOf 2 KD ≤ pCoreOf 2 Y := by
      refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 KD).trans le_sup_left) ?_
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 KD)
      refine sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 KD) ?_
      exact hDCKD'.trans (Subgroup.centralizer_le_normalizer _)
    rw [hRD] at hle
    exact ⟨CFSG.LieType.BorelTits.pCoreOf_le 2 KD hx, hDKD (hle hx)⟩
  have hm : 1 < CFSG.Open.pRank 2 KD := by
    have hmem : 4 ∈ {k | ∃ E' : Subgroup G, E' ≤ KD ∧ IsElemAbelian 2 E' ∧
        Nat.card E' = 2 ^ k} :=
      ⟨V, hVK.trans hKKD, isElemAbelian_V hKs hKa hKV hV16, by rw [hV16]; norm_num⟩
    have hbdd : BddAbove {k | ∃ E' : Subgroup G, E' ≤ KD ∧ IsElemAbelian 2 E' ∧
        Nat.card E' = 2 ^ k} := by
      refine ⟨Nat.card G, fun k hk => ?_⟩
      obtain ⟨E', -, -, hEc⟩ := hk
      have h1 : 2 ^ k ≤ Nat.card G := hEc ▸ Subgroup.card_le_card_group E'
      exact (Nat.lt_two_pow_self.trans_le h1).le
    exact lt_of_lt_of_le (by omega) (le_csSup hbdd hmem)
  have hqs : CFSG.IsQuasisimple ↥KD :=
    Vol2Native.lemma_1_2_1_five_core hLS h36 hl2 hOGD hKDc hcenter hm
  have hlistKD : CFSG.Milestones.SQTKSimpleList (↥KD ⧸ Subgroup.center ↥KD) := by
    have hSQTK : CFSG.SectionRank.IsSQTKCat ↥GD := hLS GD hOGD
    have e : ↥KD ≃* ↥(KD.subgroupOf GD) := (Subgroup.subgroupOfEquivOfLe hKDGD).symm
    have hqH : CFSG.IsQuasisimple ↥(KD.subgroupOf GD) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv e hqs
    have : IsSimpleGroup (↥(KD.subgroupOf GD) ⧸ Subgroup.center ↥(KD.subgroupOf GD)) := hqH.2.1
    have hlist' := hlist ↥GD hSQTK (KD.subgroupOf GD) (Subgroup.center ↥(KD.subgroupOf GD))
      hqH.2.2
    exact CFSG.QuasithinUnique.Ch1.sqtkSimpleList_of_mulEquiv
      (QuotientGroup.congr _ _ e
        (CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv e)) hlist'
  set T₂ := TD ⊓ Y with hT2
  have hsubY : (Y.subgroupOf GD).IsSubnormal := by
    have h1 : (KD.subgroupOf GD).IsSubnormal :=
      (CFSG.Quasithin.isSubnormal_iff_subgroupOf hKDGD).mp (subnormal_of_mem_cComp hKDc)
    have hDn : (D.subgroupOf GD).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hDGD).mpr
        (fun x hx => Subgroup.centralizer_le_normalizer (D : Set G) hx)
    have h2 : ((KD.subgroupOf GD) ⊔ D.subgroupOf GD).IsSubnormal :=
      CFSG.GroupTheory.isSubnormal_sup h1 hDn.isSubnormal
    have heq : (Y.subgroupOf GD) = KD.subgroupOf GD ⊔ D.subgroupOf GD := by
      apply Subgroup.map_injective GD.subtype_injective
      rw [Subgroup.map_subgroupOf_eq_of_le hYGD, Subgroup.map_sup,
        Subgroup.map_subgroupOf_eq_of_le hKDGD, Subgroup.map_subgroupOf_eq_of_le hDGD]
    rwa [heq]
  have hT2syl : IsSylowTwoOf T₂ Y :=
    RankOneRecog.isSylowTwoOf_inf_of_subnormal hTD hYGD hsubY
  have hT1T2 : T₁ ≤ T₂ := inf_le_inf_right Y hT0TD
  have hT1eq : T₀ ⊓ T₂ = T₁ := by
    ext x
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hx0, _, hxY⟩
      exact ⟨hx0, hxY⟩
    · rintro ⟨hx0, hxY⟩
      exact ⟨hx0, hT0TD hx0, hxY⟩
  have hrel : T₁.relIndex T₂ ≤ 2 := by
    rw [← hT1eq, Subgroup.inf_relIndex_right]
    exact (Subgroup.relIndex_le_of_le_right (inf_le_left : T₂ ≤ TD)
      (Subgroup.index_ne_zero_of_finite (H := T₀.subgroupOf TD))).trans
      hidx
  exact hExcl G KD D K V T₁ T₂ hqs hlistKD hD2 hDKD hRD hKKD hKs hKa hKV hV16 hDT1 inf_le_right
    hT1N hYN hsylT1 hT2syl hT1T2 hrel

end Main

end CFSG.Quasithin.H13.CTK
